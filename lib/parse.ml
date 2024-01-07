type kind = Mut | Val [@@deriving show]

type expr =
  | Lit of lit
  | Id of string
  | Uop of uop * expr
  | Binop of expr * binop * expr
  | If of if'
  | Sum of sum_var list
  | Prod of prod_field list
  | Block of stmt list
  | Proc of proc
  | ProcT of proc_t
  | Call of call
[@@deriving show]

and lit = Num of int | Rune of char | String of string
and uop = Not | UnaryMins

and binop =
  | Plus
  | Mins
  | Astr
  | Slsh
  | Perc
  | And
  | Or
  | Eq
  | Ne
  | Le
  | Lt
  | Dot

and if' = { cond : expr; if_branch : expr; else_branch : expr option }
and sum_var = { name : string; value : expr option }
and prod_field = Decl of decl_field | Value of expr

and decl_field = {
  kind : kind option;
  name_or_count : name_or_count;
  type' : expr option;
  value : expr option;
}

and name_or_count = Name of string | Count of int

and stmt =
  | Brk
  | Ctn
  | Ret of expr option
  | Decl of decl
  | Assign of assign
  | Loop of expr
  | Expr of expr

and decl = {
  kind : kind;
  name : string;
  type' : expr option;
  value : expr option;
}

and assign = { assignee : expr; value : expr }
and proc = { type' : proc_t; body : stmt list }
and proc_t = { args : prod_field list; return_type : expr option }
and call = { callee : expr; args : prod_field list }

type ast = expr [@@deriving show]

(* TODO: Embed positions in ast only where applicable for errors. *)

module TokenToken = struct
  include Starpath.CharToken

  type t = Lex.token

  let string_of_token = Lex.string_of_token
end

open Starpath.Make (TokenToken)
open Util

let num = satisfy_map ~expected:[ Lex.num_expected ] Lex.num_val
let rune = satisfy_map ~expected:[ Lex.rune_expected ] Lex.rune_val
let string = satisfy_map ~expected:[ Lex.string_expected ] Lex.string_val

let lit =
  num
  >>| (fun n -> Num n)
  <|> (rune >>| fun c -> Rune c)
  <|> (string >>| fun s -> String s)

let id = satisfy_map ~expected:[ Lex.id_expected ] Lex.id_val
let skip_nls = skip_while Lex.is_nl

let keyword k =
  satisfy
    ~expected:[ quoted (Lex.string_of_keyword k) ]
    (function Keyword k' when k = k' -> true | _ -> false)

let if' expr =
  keyword If *> skip_nls
  *> let* cond = expr in
     skip_nls *> keyword Then *> skip_nls
     *> let* if_branch = expr in
        let* else_branch =
          optional (skip_nls *> keyword Else *> skip_nls *> expr)
        in
        return (cond, if_branch, else_branch)

let golike_sep_by sep e =
  skip_nls
  *> optional
       (fix (fun golike_sep_by ->
            let* e1 = e in
            optional
              (skip_nls *> sep *> skip_nls
              *> let+ rest = optional golike_sep_by in
                 e1 :: Option.value ~default:[] rest)
            >>| Option.value ~default:[ e1 ]))
  >>| Option.value ~default:[]

let sum expr =
  let sum_var =
    let* name = id in
    let* value =
      optional (skip_nls *> token OpenRound *> optional expr <* token CloseRound)
    in
    let value = Option.value ~default:None value in
    return { name; value }
  in
  token OpenSquare *> golike_sep_by (token Comma) sum_var <* token CloseSquare

let kind = keyword Mut *> return Mut <|> keyword Val *> return Val

let prod expr =
  let prod_field =
    (let* kind = optional (kind <* skip_nls) in
     let* name_or_count =
       id >>| (fun s -> Name s) <|> (num >>| fun n -> Count n)
     in
     let* type' = optional (skip_nls *> token Colon *> skip_nls *> expr) in
     let* value = optional (skip_nls *> token Assign *> skip_nls *> expr) in
     if Option.is_some kind || Option.is_some type' || Option.is_some value then
       return (Decl { kind; name_or_count; type'; value })
     else
       return
         (Value
            (match name_or_count with
            | Name id -> Id id
            | Count n -> Lit (Num n))))
    <|> (expr >>| fun expr -> Value expr)
  in
  token OpenRound *> golike_sep_by (token Comma) prod_field <* token CloseRound

let decl expr =
  let* kind = kind in
  skip_nls
  *> let* name = id in
     let* type' = optional (skip_nls *> token Colon *> skip_nls *> expr) in
     let* value = optional (skip_nls *> token Assign *> skip_nls *> expr) in
     return { kind; name; type'; value }

let assign expr =
  let* assignee = expr in
  skip_nls *> token Assign *> skip_nls
  *> let* value = expr in
     return { assignee; value }

let loop expr = keyword Loop *> skip_nls *> expr

let stmt expr =
  keyword Brk *> return Brk
  <|> keyword Ctn *> return Ctn
  <|> (keyword Ret *> skip_nls *> optional expr >>| fun expr_opt -> Ret expr_opt)
  <|> (decl expr >>| fun decl : stmt -> Decl decl)
  <|> (assign expr >>| fun assign -> Assign assign)
  <|> (loop expr >>| fun expr -> Loop expr)
  <|> (expr >>| fun expr -> Expr expr)

let block expr =
  token OpenCurly *> skip_nls
  *> sep_by (token Nl <|> token Semi <* skip_nls) (stmt expr)
  <* skip_nls <* token CloseCurly

let proc_t expr =
  keyword Proc *> skip_nls
  *> let* args = prod expr in
     let* return_type =
       optional (skip_nls *> token Colon *> skip_nls *> expr)
     in
     return { args; return_type }

let proc expr =
  let* type' = proc_t expr in
  skip_nls
  *> let* body = block expr in
     return { type'; body }

let expr =
  fix (fun expr ->
      let prim_expr =
        lit
        >>| (fun l -> Lit l)
        <|> (id >>| fun s -> Id s)
        <|> ( if' expr >>| fun (cond, if_branch, else_branch) ->
              If { cond; if_branch; else_branch } )
        <|> (sum expr >>| fun vars -> Sum vars)
        <|> (prod expr >>| fun fields -> Prod fields)
        <|> (block expr >>| fun stmts -> Block stmts)
        <|> (proc expr >>| fun proc -> Proc proc)
        <|> (proc_t expr >>| fun proc_t -> ProcT proc_t)
      in
      let dot_expr =
        let* accessee = prim_expr in
        let* accessors = repeat (skip_nls *> token Dot *> skip_nls *> id) in
        return
          (List.fold_left
             (fun accessee accessor -> Binop (accessee, Dot, Id accessor))
             accessee accessors)
      in
      let call_expr =
        let* callee = dot_expr in
        let* argss = repeat (skip_nls *> prod expr) in
        return
          (List.fold_left
             (fun callee args -> Call { callee; args })
             callee argss)
      in
      let uop_expr =
        let* uops =
          repeat
            (token LNot *> return Not
            <|> token Mins *> return UnaryMins
            <* skip_nls)
        in
        let* expr = call_expr in
        return (List.fold_left (fun expr uop -> Uop (uop, expr)) expr uops)
      in
      let* lhs1 = uop_expr in
      let* rest =
        repeat
          (skip_nls
          *> let* binop =
               token Plus *> return Plus
               <|> token Mins *> return Mins
               <|> token Astr *> return Astr
               <|> token Slsh *> return Slsh
               <|> token Perc *> return Perc
               <|> token LAnd *> return And
               <|> token LOr *> return Or
               <|> token Eq *> return Eq
               <|> token Ne *> return Ne
               <|> token Le *> return Le
               <|> token Lt *> return Lt
             in
             skip_nls
             *> let* rhs = uop_expr in
                return (binop, rhs))
      in
      return
        (List.fold_left
           (fun lhs (binop, rhs) -> Binop (lhs, binop, rhs))
           lhs1 rest))

let ast : ast t = skip_nls *> expr <* skip_nls

exception ParseError of string

let () =
  Printexc.register_printer (function
    | ParseError msg -> Some (Printf.sprintf "parse error: %s" msg)
    | _ -> None)

let parse text =
  let tokens = Lex.lex text in
  match parse tokens ast with
  | Ok ast -> ast
  | Error s -> raise (ParseError (string_of_parse_error s))

let dump = parse >> show_ast >> print_endline

[@@@coverage off]

let assert_raises f =
  try
    let _ = f () in
    false
  with _ -> true

[@@@coverage on]

let%expect_test _ =
  dump "0";
  [%expect {| (Parse.Lit (Parse.Num 0)) |}]

let%expect_test _ =
  dump "0123456789";
  [%expect {| (Parse.Lit (Parse.Num 123456789)) |}]

let%expect_test _ =
  dump "' '";
  [%expect {| (Parse.Lit (Parse.Rune ' ')) |}]

let%expect_test _ =
  dump {|'"'|};
  [%expect {| (Parse.Lit (Parse.Rune '"')) |}]

let%test _ = assert_raises (fun () -> parse "'''")

let%expect_test _ =
  dump {|""|};
  [%expect {| (Parse.Lit (Parse.String "")) |}]

let%expect_test _ =
  dump {|"foo bar baz"|};
  [%expect {| (Parse.Lit (Parse.String "foo bar baz")) |}]

let%test _ = assert_raises (fun () -> parse {|"""|})

let%expect_test _ =
  dump "_";
  [%expect {| (Parse.Id "_") |}]

let%expect_test _ =
  dump "foo_bar";
  [%expect {| (Parse.Id "foo_bar") |}]

let%expect_test _ =
  dump "FooBar123";
  [%expect {| (Parse.Id "FooBar123") |}]

let%expect_test _ =
  dump "!foo";
  [%expect {| (Parse.Uop (Parse.Not, (Parse.Id "foo"))) |}]

let%expect_test _ =
  dump "- foo";
  [%expect {| (Parse.Uop (Parse.UnaryMins, (Parse.Id "foo"))) |}]

let%expect_test _ =
  dump "if a then b";
  [%expect
    {|
    (Parse.If
       { Parse.cond = (Parse.Id "a"); if_branch = (Parse.Id "b");
         else_branch = None }) |}]

let%expect_test _ =
  dump "if a then b else c";
  [%expect
    {|
    (Parse.If
       { Parse.cond = (Parse.Id "a"); if_branch = (Parse.Id "b");
         else_branch = (Some (Parse.Id "c")) }) |}]

let%expect_test _ =
  dump "[]";
  [%expect {| (Parse.Sum []) |}]

let%expect_test _ =
  dump "[   ]";
  [%expect {| (Parse.Sum []) |}]

let%expect_test _ =
  dump "[red, green, blue]";
  [%expect
    {|
    (Parse.Sum
       [{ Parse.name = "red"; value = None };
         { Parse.name = "green"; value = None };
         { Parse.name = "blue"; value = None }]) |}]

let%expect_test _ =
  dump {|
  [
    red(int),
    green(string),
    blue(bool),
  ]
  |};
  [%expect
    {|
    (Parse.Sum
       [{ Parse.name = "red"; value = (Some (Parse.Id "int")) };
         { Parse.name = "green"; value = (Some (Parse.Id "string")) };
         { Parse.name = "blue"; value = (Some (Parse.Id "bool")) }]) |}]

let%test _ = assert_raises (fun () -> parse {|
  (
    foo,
    bar
  )
  |})

let%expect_test _ =
  dump "()";
  [%expect {| (Parse.Prod []) |}]

let%expect_test _ =
  dump "(   )";
  [%expect {| (Parse.Prod []) |}]

let%expect_test _ =
  dump "(5, false, \"foo\"\t)";
  [%expect
    {|
    (Parse.Prod
       [(Parse.Value (Parse.Lit (Parse.Num 5)));
         (Parse.Value (Parse.Id "false"));
         (Parse.Value (Parse.Lit (Parse.String "foo")))]) |}]

let%expect_test _ =
  dump "(5: int)";
  [%expect
    {|
    (Parse.Prod
       [(Parse.Decl
           { Parse.kind = None; name_or_count = (Parse.Count 5);
             type' = (Some (Parse.Id "int")); value = None })
         ]) |}]

let%expect_test _ =
  dump {|(a = 5, b = false, c = "foo")|};
  [%expect
    {|
    (Parse.Prod
       [(Parse.Decl
           { Parse.kind = None; name_or_count = (Parse.Name "a"); type' = None;
             value = (Some (Parse.Lit (Parse.Num 5))) });
         (Parse.Decl
            { Parse.kind = None; name_or_count = (Parse.Name "b"); type' = None;
              value = (Some (Parse.Id "false")) });
         (Parse.Decl
            { Parse.kind = None; name_or_count = (Parse.Name "c"); type' = None;
              value = (Some (Parse.Lit (Parse.String "foo"))) })
         ]) |}]

let%expect_test _ =
  dump {|(a: int, b: bool, c: string)|};
  [%expect
    {|
    (Parse.Prod
       [(Parse.Decl
           { Parse.kind = None; name_or_count = (Parse.Name "a");
             type' = (Some (Parse.Id "int")); value = None });
         (Parse.Decl
            { Parse.kind = None; name_or_count = (Parse.Name "b");
              type' = (Some (Parse.Id "bool")); value = None });
         (Parse.Decl
            { Parse.kind = None; name_or_count = (Parse.Name "c");
              type' = (Some (Parse.Id "string")); value = None })
         ]) |}]

let%expect_test _ =
  dump {|(val a = 5, val b = false, mut c = "foo")|};
  [%expect
    {|
    (Parse.Prod
       [(Parse.Decl
           { Parse.kind = (Some Parse.Val); name_or_count = (Parse.Name "a");
             type' = None; value = (Some (Parse.Lit (Parse.Num 5))) });
         (Parse.Decl
            { Parse.kind = (Some Parse.Val); name_or_count = (Parse.Name "b");
              type' = None; value = (Some (Parse.Id "false")) });
         (Parse.Decl
            { Parse.kind = (Some Parse.Mut); name_or_count = (Parse.Name "c");
              type' = None; value = (Some (Parse.Lit (Parse.String "foo"))) })
         ]) |}]

let%expect_test _ =
  dump {|(val a: int, val b: bool, mut c: string)|};
  [%expect
    {|
    (Parse.Prod
       [(Parse.Decl
           { Parse.kind = (Some Parse.Val); name_or_count = (Parse.Name "a");
             type' = (Some (Parse.Id "int")); value = None });
         (Parse.Decl
            { Parse.kind = (Some Parse.Val); name_or_count = (Parse.Name "b");
              type' = (Some (Parse.Id "bool")); value = None });
         (Parse.Decl
            { Parse.kind = (Some Parse.Mut); name_or_count = (Parse.Name "c");
              type' = (Some (Parse.Id "string")); value = None })
         ]) |}]

let%expect_test _ =
  dump {|(val a: int = 5, val b: bool = false, mut c: string = "foo")|};
  [%expect
    {|
    (Parse.Prod
       [(Parse.Decl
           { Parse.kind = (Some Parse.Val); name_or_count = (Parse.Name "a");
             type' = (Some (Parse.Id "int"));
             value = (Some (Parse.Lit (Parse.Num 5))) });
         (Parse.Decl
            { Parse.kind = (Some Parse.Val); name_or_count = (Parse.Name "b");
              type' = (Some (Parse.Id "bool")); value = (Some (Parse.Id "false"))
              });
         (Parse.Decl
            { Parse.kind = (Some Parse.Mut); name_or_count = (Parse.Name "c");
              type' = (Some (Parse.Id "string"));
              value = (Some (Parse.Lit (Parse.String "foo"))) })
         ]) |}]

let%expect_test _ =
  dump "{}";
  [%expect {| (Parse.Block []) |}]

let%expect_test _ =
  dump "{   }";
  [%expect {| (Parse.Block []) |}]

let%expect_test _ =
  dump "{\n \t \n \r }";
  [%expect {| (Parse.Block []) |}]

let%expect_test _ =
  dump "{brk;ctn}";
  [%expect {| (Parse.Block [Parse.Brk; Parse.Ctn]) |}]

let%expect_test _ =
  dump
    {|
  {
    val i: int = 0
    mut j
    loop { }
    ret bool
    j = i
    "yoo"
  }
  |};
  [%expect
    {|
    (Parse.Block
       [(Parse.Decl
           { Parse.kind = Parse.Val; name = "i"; type' = (Some (Parse.Id "int"));
             value = (Some (Parse.Lit (Parse.Num 0))) });
         (Parse.Decl
            { Parse.kind = Parse.Mut; name = "j"; type' = None; value = None });
         (Parse.Loop (Parse.Block [])); (Parse.Ret (Some (Parse.Id "bool")));
         (Parse.Assign
            { Parse.assignee = (Parse.Id "j"); value = (Parse.Id "i") });
         (Parse.Expr (Parse.Lit (Parse.String "yoo")))]) |}]

let%expect_test _ =
  dump "proc()";
  [%expect {| (Parse.ProcT { Parse.args = []; return_type = None }) |}]

let%expect_test _ =
  dump "proc(mut a: int = 5, val b: string): int";
  [%expect
    {|
    (Parse.ProcT
       { Parse.args =
         [(Parse.Decl
             { Parse.kind = (Some Parse.Mut); name_or_count = (Parse.Name "a");
               type' = (Some (Parse.Id "int"));
               value = (Some (Parse.Lit (Parse.Num 5))) });
           (Parse.Decl
              { Parse.kind = (Some Parse.Val); name_or_count = (Parse.Name "b");
                type' = (Some (Parse.Id "string")); value = None })
           ];
         return_type = (Some (Parse.Id "int")) }) |}]

let%expect_test _ =
  dump "proc() {}";
  [%expect
    {|
    (Parse.Proc
       { Parse.type' = { Parse.args = []; return_type = None }; body = [] }) |}]

let%expect_test _ =
  dump {|
  proc(mut a: int = 5): string { ret "foo" }
  |};
  [%expect
    {|
    (Parse.Proc
       { Parse.type' =
         { Parse.args =
           [(Parse.Decl
               { Parse.kind = (Some Parse.Mut); name_or_count = (Parse.Name "a");
                 type' = (Some (Parse.Id "int"));
                 value = (Some (Parse.Lit (Parse.Num 5))) })
             ];
           return_type = (Some (Parse.Id "string")) };
         body = [(Parse.Ret (Some (Parse.Lit (Parse.String "foo"))))] }) |}]

let%expect_test _ =
  dump "{ foo() }";
  [%expect
    {|
    (Parse.Block
       [(Parse.Expr (Parse.Call { Parse.callee = (Parse.Id "foo"); args = [] }))]) |}]

let%expect_test _ =
  dump "foo (a) (b)";
  [%expect
    {|
    (Parse.Call
       { Parse.callee =
         (Parse.Call
            { Parse.callee = (Parse.Id "foo");
              args = [(Parse.Value (Parse.Id "a"))] });
         args = [(Parse.Value (Parse.Id "b"))] }) |}]

let%expect_test _ =
  dump "1 + 2 - 3 * 4 / 5 % 6 && 7 || 9 == 10 != 11 < 12 <= 13 . hi";
  [%expect
    {|
    (Parse.Binop (
       (Parse.Binop (
          (Parse.Binop (
             (Parse.Binop (
                (Parse.Binop (
                   (Parse.Binop (
                      (Parse.Binop (
                         (Parse.Binop (
                            (Parse.Binop (
                               (Parse.Binop (
                                  (Parse.Binop ((Parse.Lit (Parse.Num 1)),
                                     Parse.Plus, (Parse.Lit (Parse.Num 2)))),
                                  Parse.Mins, (Parse.Lit (Parse.Num 3)))),
                               Parse.Astr, (Parse.Lit (Parse.Num 4)))),
                            Parse.Slsh, (Parse.Lit (Parse.Num 5)))),
                         Parse.Perc, (Parse.Lit (Parse.Num 6)))),
                      Parse.And, (Parse.Lit (Parse.Num 7)))),
                   Parse.Or, (Parse.Lit (Parse.Num 9)))),
                Parse.Eq, (Parse.Lit (Parse.Num 10)))),
             Parse.Ne, (Parse.Lit (Parse.Num 11)))),
          Parse.Lt, (Parse.Lit (Parse.Num 12)))),
       Parse.Le,
       (Parse.Binop ((Parse.Lit (Parse.Num 13)), Parse.Dot, (Parse.Id "hi"))))) |}]

let%expect_test _ =
  dump "-1 + -3";
  [%expect
    {|
    (Parse.Binop ((Parse.Uop (Parse.UnaryMins, (Parse.Lit (Parse.Num 1)))),
       Parse.Plus, (Parse.Uop (Parse.UnaryMins, (Parse.Lit (Parse.Num 3)))))) |}]
