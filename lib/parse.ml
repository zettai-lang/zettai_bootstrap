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

(* TODO: Convert to separate lex+parse steps to improve error readability. *)
(* TODO: Embed positions in ast only where applicable for errors. *)

open Starpath.StringCombinators
open Util

let implode = List.to_seq >> String.of_seq
let is_digit = function '0' .. '9' -> true | _ -> false

let num =
  take_while1 ~expected:[ "number" ] is_digit >>| (implode >> int_of_string)

let rune = token '\'' *> token_not '\'' <* token '\''
let string' = token '"' *> take_while (( <> ) '"') <* token '"'

let lit =
  num
  >>| (fun n -> Num n)
  <|> (rune >>| fun c -> Rune c)
  <|> (string' >>| fun s -> String (implode s))

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
let is_id_start c = is_alpha c || c == '_'
let is_id_cont c = is_id_start c || is_digit c

let reserved =
  [ "if"; "then"; "else"; "mut"; "val"; "loop"; "proc"; "brk"; "ctn"; "ret" ]

let id =
  let* pos, start = satisfy ~expected:[ "[a-zA-Z_]" ] is_id_start |> pos in
  let* rest = take_while is_id_cont in
  let id = String.make 1 start ^ implode rest in
  if List.exists (( = ) id) reserved then
    fail
      {
        pos;
        expected = [ "identifier" ];
        actual = "reserved keyword: \"" ^ String.escaped id ^ "\"";
      }
  else return id

let is_space = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false
let skip_space = skip_while is_space

let keyword s =
  let* tp = string s *> peek |> pos in
  match tp with
  | pos, Some t when is_id_cont t ->
      fail
        {
          pos;
          expected = [ "[^a-zA-Z0-9_]" ];
          actual = "'" ^ Char.escaped t ^ "'";
        }
  | _ -> return s

let if' expr =
  keyword "if" *> skip_space
  *> let* cond = expr in
     skip_space *> keyword "then" *> skip_space
     *> let* if_branch = expr in
        let* else_branch =
          optional (skip_space *> keyword "else" *> skip_space *> expr)
        in
        return (cond, if_branch, else_branch)

let is_horiz_space = function ' ' | '\t' -> true | _ -> false
let skip_horiz_space = skip_while is_horiz_space

let golike_sep_by sep e =
  skip_space
  *> optional
       (fix (fun golike_sep_by ->
            let* e1 = e in
            optional
              (skip_space *> sep *> skip_space
              *> let+ rest = optional golike_sep_by in
                 e1 :: Option.value ~default:[] rest)
            >>| Option.value ~default:[ e1 ]))
  >>| Option.value ~default:[] <* skip_horiz_space

let sum expr =
  let sum_var =
    let* name = id in
    let* value =
      optional (skip_space *> token '(' *> optional expr <* token ')')
    in
    let value = Option.value ~default:None value in
    return { name; value }
  in
  token '[' *> golike_sep_by (token ',') sum_var <* token ']'

let kind = keyword "mut" *> return Mut <|> keyword "val" *> return Val

let prod expr =
  let prod_field =
    (let* kind = optional (kind <* skip_space) in
     let* name_or_count =
       id >>| (fun s -> Name s) <|> (num >>| fun n -> Count n)
     in
     let* type' = optional (skip_space *> token ':' *> skip_space *> expr) in
     let* value = optional (skip_space *> token '=' *> skip_space *> expr) in
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
  token '(' *> golike_sep_by (token ',') prod_field <* token ')'

let decl expr =
  let* kind = kind in
  skip_space
  *> let* name = id in
     let* type' = optional (skip_space *> token ':' *> skip_space *> expr) in
     let* value = optional (skip_space *> token '=' *> skip_space *> expr) in
     return { kind; name; type'; value }

let assign expr =
  let* assignee = expr in
  skip_space *> token '=' *> skip_space
  *> let* value = expr in
     return { assignee; value }

let loop expr = keyword "loop" *> skip_space *> expr

let stmt expr =
  keyword "brk" *> return Brk
  <|> keyword "ctn" *> return Ctn
  <|> ( keyword "ret" *> skip_space *> optional expr >>| fun expr_opt ->
        Ret expr_opt )
  <|> (decl expr >>| fun decl : stmt -> Decl decl)
  <|> (assign expr >>| fun assign -> Assign assign)
  <|> (loop expr >>| fun expr -> Loop expr)
  <|> (expr >>| fun expr -> Expr expr)

let block expr =
  token '{' *> skip_space
  *> sep_by
       (skip_horiz_space *> (token '\n' <|> token ';') <* skip_space)
       (stmt expr)
  <* skip_space <* token '}'

let proc_t expr =
  keyword "proc" *> skip_space
  *> let* args = prod expr in
     let* return_type =
       optional (skip_space *> token ':' *> skip_space *> expr)
     in
     return { args; return_type }

let proc expr =
  let* type' = proc_t expr in
  skip_space
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
        let* accessors = repeat (skip_space *> token '.' *> skip_space *> id) in
        return
          (List.fold_left
             (fun accessee accessor -> Binop (accessee, Dot, Id accessor))
             accessee accessors)
      in
      let call_expr =
        let* callee = dot_expr in
        let* argss = repeat (skip_space *> prod expr) in
        return
          (List.fold_left
             (fun callee args -> Call { callee; args })
             callee argss)
      in
      let uop_expr =
        let* uops =
          repeat
            (token '!' *> return Not
            <|> token '-' *> return UnaryMins
            <* skip_space)
        in
        let* expr = call_expr in
        return (List.fold_left (fun expr uop -> Uop (uop, expr)) expr uops)
      in
      let* lhs1 = uop_expr in
      let* rest =
        repeat
          (skip_space
          *> let* binop =
               token '+' *> return Plus
               <|> token '-' *> return Mins
               <|> token '*' *> return Astr
               <|> token '/' *> return Slsh
               <|> token '%' *> return Perc
               <|> string "&&" *> return And
               <|> string "||" *> return Or
               <|> string "==" *> return Eq
               <|> string "!=" *> return Ne
               <|> string "<=" *> return Le
               <|> token '<' *> return Lt
             in
             skip_space
             *> let* rhs = uop_expr in
                return (binop, rhs))
      in
      return
        (List.fold_left
           (fun lhs (binop, rhs) -> Binop (lhs, binop, rhs))
           lhs1 rest))

let ast : ast t = skip_space *> expr <* skip_space

exception ParseError of string

let () =
  Printexc.register_printer (function
    | ParseError msg -> Some (Printf.sprintf "parse error: %s" msg)
    | _ -> None)

let parse text =
  match parse_string text ast with
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
