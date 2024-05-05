let pp_string_pos fmt ({ row; col } : Starpath.string_pos) =
  Format.fprintf fmt "@[<2>{ ";
  Format.fprintf fmt "@[Starpath.row =@ %d;@ " row;
  Format.fprintf fmt "@[col =@ %d" col;
  Format.fprintf fmt "@ }@]"

type kind = Mut | Val [@@deriving show]

type lit = Num of int | Rune of char | String of string
[@@deriving show, variants]

type name_or_count = Name of string | Count of int [@@deriving show, variants]
type uop = Not | UnaryMins | Ref | MutRef | Deref [@@deriving show]

type binop =
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
[@@deriving show]

type 'p expr =
  | Lit of lit
  | Id of 'p * string
  | Uop of 'p * uop * 'p expr
  | Binop of 'p * 'p expr * binop * 'p * 'p expr
  | If of 'p if'
  | Sum of 'p sum_var list
  | Prod of 'p * 'p prod
  | Block of 'p stmt list
  | Proc of 'p proc
  | ProcT of 'p * 'p proc_t
  | Call of 'p * 'p call
[@@deriving map, show]

and 'p if' = {
  cond : 'p * 'p expr;
  if_branch : 'p expr;
  else_branch : 'p expr option;
}

and 'p sum_var = { name : string; value : ('p * 'p expr) option }
and 'p prod = { rec' : bool; fields : 'p prod_field list }
and 'p prod_field = Decl of 'p decl_field | Value of 'p * 'p expr

and 'p decl_field = {
  kind : ('p * kind) option;
  name_or_count : 'p * name_or_count;
  type' : ('p * 'p expr) option;
  value : 'p expr option;
}

and 'p stmt =
  | Brk of 'p
  | Ctn of 'p
  | Ret of 'p * 'p expr option
  | Decl of 'p * 'p decl
  | Assign of 'p assign
  | Loop of 'p expr
  | Expr of 'p expr

and 'p decl = {
  kind : kind;
  name : 'p * string;
  type' : 'p expr option;
  value : 'p expr option;
}

and 'p assign = { assignee : 'p expr; value : 'p expr }
and 'p proc = { type' : 'p proc_t; body : 'p stmt list }
and 'p proc_t = { args : 'p * 'p prod; return_type : ('p * 'p expr) option }
and 'p call = { callee : 'p expr; args : 'p prod }

type 'p ast = 'p expr [@@deriving map, show]

open Util

module Parser (Combinators : Starpath.CharCombinators) = struct
  open Combinators

  let implode = List.to_seq >> String.of_seq
  let is_digit = function '0' .. '9' -> true | _ -> false

  let num' =
    take_while1 ~expected:[ "<NUM>" ] is_digit >>| (implode >> int_of_string)

  (* TODO: Support escape sequences. *)
  let rune' = token '\'' @> token_not '\'' <* token '\''
  let string' = token '"' *> take_while (( <> ) '"') <* token '"'

  let lit =
    num' >>| num <|> (rune' >>| rune)
    <|> (string' >>| fun s -> String (implode s))

  let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
  let is_id_start c = is_alpha c || c == '_'
  let is_id_cont c = is_id_start c || is_digit c

  let reserved =
    [
      "if";
      "then";
      "else";
      "mut";
      "val";
      "loop";
      "proc";
      "brk";
      "ctn";
      "ret";
      "rec";
    ]

  let id =
    let* pos, start = satisfy ~expected:[ "<IDENTIFIER>" ] is_id_start |> pos in
    let* rest = take_while is_id_cont in
    let id = String.make 1 start ^ implode rest in
    if List.exists (( = ) id) reserved then
      fail
        {
          pos;
          expected = [ "<IDENTIFIER>" ];
          actual = "\"" ^ String.escaped id ^ "\" (keyword)";
        }
    else return id

  let skip_space =
    skip_while @@ function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

  let ( *>> ) r1 r2 = r1 *> skip_space *> r2
  let ( @>> ) r1 r2 = r1 @> (skip_space *> r2)
  let ( <<* ) r1 r2 = r1 <* skip_space <* r2
  let ( ~>> ) r = skip_space *> r

  let keyword s =
    let* op, _ = peek |> pos in
    let* tp = string s *> peek |> pos in
    match tp with
    | pos, Some t when is_id_cont t ->
        fail
          {
            pos;
            expected = [ "[^a-zA-Z0-9_]" ];
            actual = "'" ^ Char.escaped t ^ "'";
          }
    | _ -> return_at op s

  let if' expr =
    keyword "if"
    *>> let* cond = expr |> pos in
        ~>>(keyword "then")
        *>> let* if_branch = expr in
            let+ else_branch = optional (~>>(keyword "else") *>> expr) in
            (cond, if_branch, else_branch)

  let skip_horiz_space =
    skip_while @@ function ' ' | '\t' -> true | _ -> false

  let golike_sep_by sep e =
    skip_space
    *> optional_or
         (fix (fun golike_sep_by ->
              let* e1 = e in
              optional_or
                (~>>sep
                *>> let+ rest = optional_or golike_sep_by ~default:[] in
                    e1 :: rest)
                ~default:[ e1 ]))
         ~default:[]
    <* skip_horiz_space

  let sum expr =
    let sum_var =
      let* name = id in
      let+ value =
        optional_or
          ~>>(token '(' *> optional (expr |> pos) <* token ')')
          ~default:None
      in
      { name; value }
    in
    token '[' @> golike_sep_by (token ',') sum_var <* token ']'

  let kind = keyword "mut" @> return Mut <|> keyword "val" @> return Val

  let prod expr =
    let prod_field =
      (let* kind = optional (kind |> pos <* skip_space) in
       let* name_or_count = id >>| name <|> (num' >>| count) |> pos in
       let* type' = optional (~>>(token ':') *>> expr |> pos) in
       let+ value = optional (~>>(token '=') *>> expr) in
       if Option.is_some kind || Option.is_some type' || Option.is_some value
       then Decl { kind; name_or_count; type'; value }
       else
         let expr =
           match name_or_count with
           | p, Name id -> Id (p, id)
           | _, Count n -> Lit (Num n)
         in
         Value (fst name_or_count, expr))
      <* lookahead
           (~>>(token ',' *> return ()) <|> (skip_horiz_space <* token ')'))
      <|> (expr |> pos
          >>| (fun (p, expr) -> Value (p, expr))
          <* lookahead
               (~>>(token ',' *> return ()) <|> (skip_horiz_space <* token ')'))
          )
    in
    let* rec' = optional (keyword "rec" <* skip_space) >>| Option.is_some in
    let+ fields =
      token '(' @> golike_sep_by (token ',') prod_field <* token ')'
    in
    { rec'; fields }

  let decl expr =
    let* p, _ = peek |> pos in
    let* kind = kind in
    let* name = ~>>id |> pos in
    let* type' = optional (~>>(token ':') *>> expr) in
    let+ value = optional (~>>(token '=') *>> expr) in
    (p, { kind; name; type'; value })

  let assign expr =
    let* assignee = expr in
    ~>>(token '='
       *>> let+ value = expr in
           { assignee; value })

  let loop expr = keyword "loop" *>> expr

  let stmt expr =
    keyword "brk" |> pos
    >>| (fun (p, _) -> Brk p)
    <|> (keyword "ctn" |> pos >>| fun (p, _) -> Ctn p)
    <|> ( keyword "ret" @>> optional expr |> pos >>| fun (p, expr_opt) ->
          Ret (p, expr_opt) )
    <|> (decl expr >>| fun (p, decl) : _ stmt -> Decl (p, decl))
    <|> (assign expr >>| fun assign -> Assign assign)
    <|> (loop expr >>| fun expr -> Loop expr)
    <|> (expr >>| fun expr -> Expr expr)

  let block expr =
    token '{'
    @>> sep_by
          (skip_horiz_space *> (token '\n' <|> token ';') <* skip_space)
          (stmt expr)
    <<* token '}'

  let proc_t expr =
    let* p, _ = keyword "proc" |> pos in
    let* args = ~>>(prod expr) |> pos in
    let+ return_type = optional (~>>(token ':') *>> (expr |> pos)) in
    (p, { args; return_type })

  let proc expr =
    let* _, type' = proc_t expr in
    ~>>(let+ body = block expr in
        { type'; body })

  let expr =
    fix (fun expr ->
        let prim_expr =
          lit
          >>| (fun l -> Lit l)
          <|> (id |> pos >>| fun (p, s) -> Id (p, s))
          <|> ( if' expr >>| fun (cond, if_branch, else_branch) ->
                If { cond; if_branch; else_branch } )
          <|> (sum expr >>| fun vars -> Sum vars)
          <|> (prod expr |> pos >>| fun (p, prod) -> Prod (p, prod))
          <|> (block expr >>| fun stmts -> Block stmts)
          <|> (proc expr >>| fun proc -> Proc proc)
          <|> (proc_t expr >>| fun (p, proc_t) -> ProcT (p, proc_t))
        in
        let call_dot_expr =
          let* p, operand = prim_expr |> pos in
          let+ accessors =
            repeat
              ~>>(token '.' *>> (id |> pos >>| Either.left)
                 <|> (prod expr >>| Either.right))
          in
          List.fold_left
            (fun (p, accessee) -> function
              | Either.Left (accessor_pos, accessor) ->
                  ( p,
                    Binop
                      ( p,
                        accessee,
                        Dot,
                        accessor_pos,
                        Id (accessor_pos, accessor) ) )
              | Right args -> (p, Call (p, { callee = accessee; args })))
            (p, operand) accessors
          |> snd
        in
        let uop_expr =
          let* uops =
            repeat
              (token '!' @> return Not
              <|> token '-' @> return UnaryMins
              <|> token '&' @> keyword "mut" @> return MutRef
              <|> token '&' @> return Ref
              <|> token '*' @> return Deref
              |> pos <* skip_space)
          in
          let+ expr = call_dot_expr in
          List.fold_right (fun (p, uop) expr -> Uop (p, uop, expr)) uops expr
        in
        let* p, lhs1 = uop_expr |> pos in
        let+ rest =
          repeat
            ~>>(let* binop =
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
                ~>>(let+ rhs = uop_expr |> pos in
                    (binop, rhs)))
        in
        List.fold_left
          (fun lhs (binop, (rhs_pos, rhs)) ->
            Binop (p, lhs, binop, rhs_pos, rhs))
          lhs1 rest)

  let ast = skip_space *> expr <* skip_space
end

exception ParseError of string

let () =
  Printexc.register_printer @@ function
  | ParseError msg -> Some (Printf.sprintf "parse error: %s" msg)
  | _ -> None

let preprocess = Str.global_replace (Str.regexp "#.*$") ""

let parse path =
  let open Parser (Starpath.FileCombinators) in
  let open Starpath.FileCombinators in
  match parse_file path ~preprocess ast with
  | Ok ast -> ast
  | Error s -> raise (ParseError (string_of_parse_error s))

let parse_string s =
  let open Parser (Starpath.StringCombinators) in
  let open Starpath.StringCombinators in
  match parse_string (preprocess s) ast with
  | Ok ast -> ast
  | Error s -> raise (ParseError (string_of_parse_error s))

let dump : string -> unit =
  parse_string >> show_ast pp_string_pos >> print_endline

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
  [%expect {| (Parse.Id ({ Starpath.row = 1; col = 1 }, "_")) |}]

let%expect_test _ =
  dump "foo_bar";
  [%expect {| (Parse.Id ({ Starpath.row = 1; col = 1 }, "foo_bar")) |}]

let%expect_test _ =
  dump "FooBar123";
  [%expect {| (Parse.Id ({ Starpath.row = 1; col = 1 }, "FooBar123")) |}]

let%expect_test _ =
  dump "!foo";
  [%expect
    {|
      (Parse.Uop (
         { Starpath.row = 1; col = 1 }, Parse.Not,
           (Parse.Id ({ Starpath.row = 1; col = 2 }, "foo")))) |}]

let%expect_test _ =
  dump "- foo";
  [%expect
    {|
    (Parse.Uop (
       { Starpath.row = 1; col = 1 }, Parse.UnaryMins,
         (Parse.Id ({ Starpath.row = 1; col = 3 }, "foo")))) |}]

let%expect_test _ =
  dump "&foo";
  [%expect
    {|
    (Parse.Uop (
       { Starpath.row = 1; col = 1 }, Parse.Ref,
         (Parse.Id ({ Starpath.row = 1; col = 2 }, "foo")))) |}]

let%expect_test _ =
  dump "&mut foo";
  [%expect
    {|
    (Parse.Uop (
       { Starpath.row = 1; col = 1 }, Parse.MutRef,
         (Parse.Id ({ Starpath.row = 1; col = 6 }, "foo")))) |}]

let%expect_test _ =
  dump "*foo";
  [%expect
    {|
    (Parse.Uop (
       { Starpath.row = 1; col = 1 }, Parse.Deref,
         (Parse.Id ({ Starpath.row = 1; col = 2 }, "foo")))) |}]

let%expect_test _ =
  dump "*&foo";
  [%expect
    {|
    (Parse.Uop (
       { Starpath.row = 1; col = 1 }, Parse.Deref,
         (Parse.Uop (
            { Starpath.row = 1; col = 2 }, Parse.Ref,
              (Parse.Id ({ Starpath.row = 1; col = 3 }, "foo")))))) |}]

let%expect_test _ =
  dump "if a then b";
  [%expect
    {|
    (Parse.If
       { Parse.cond =
         ({ Starpath.row = 1; col = 4 },
            (Parse.Id ({ Starpath.row = 1; col = 4 }, "a")));
            if_branch =
            (Parse.Id ({ Starpath.row = 1; col = 11 }, "b")); else_branch = None
               }) |}]

let%expect_test _ =
  dump "if a then b else c";
  [%expect
    {|
    (Parse.If
       { Parse.cond =
         ({ Starpath.row = 1; col = 4 },
            (Parse.Id ({ Starpath.row = 1; col = 4 }, "a")));
            if_branch =
            (Parse.Id ({ Starpath.row = 1; col = 11 }, "b"));
               else_branch =
               (Some (Parse.Id ({ Starpath.row = 1; col = 18 }, "c"))) }) |}]

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
       [{ Parse.name = "red";
          value =
          (Some ({ Starpath.row = 3; col = 9 },
                   (Parse.Id ({ Starpath.row = 3; col = 9 }, "int")))) };
                   { Parse.name = "green";
                     value =
                     (Some ({ Starpath.row = 4; col = 11 },
                              (Parse.Id (
                                 { Starpath.row = 4; col = 11 }, "string"))))
                              };
                              { Parse.name = "blue";
                                value =
                                (Some ({ Starpath.row = 5; col = 10 },
                                         (Parse.Id (
                                            { Starpath.row = 5; col = 10 },
                                              "bool"))))
                                         }]) |}]

let%test _ = assert_raises (fun () -> parse {|
  (
    foo,
    bar
  )
  |})

let%expect_test _ =
  dump "()";
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 }, { Parse.rec' = false; fields = [] })) |}]

let%expect_test _ =
  dump "(   )";
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 }, { Parse.rec' = false; fields = [] })) |}]

let%expect_test _ =
  dump "(5, false, \"foo\"\t)";
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 },
         { Parse.rec' = false;
           fields =
           [(Parse.Value (
               { Starpath.row = 1; col = 2 }, (Parse.Lit (Parse.Num 5))));
                 (Parse.Value (
                    { Starpath.row = 1; col = 5 },
                      (Parse.Id ({ Starpath.row = 1; col = 5 }, "false"))));
                         (Parse.Value (
                            { Starpath.row = 1; col = 12 },
                              (Parse.Lit (Parse.String "foo"))))]
                         }
                      )) |}]

let%expect_test _ =
  dump "(5: int)";
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 },
         { Parse.rec' = false;
           fields =
           [(Parse.Decl
               { Parse.kind = None;
                 name_or_count =
                 ({ Starpath.row = 1; col = 2 }, (Parse.Count 5));
                  type' =
                  (Some ({ Starpath.row = 1; col = 5 },
                           (Parse.Id ({ Starpath.row = 1; col = 5 }, "int"))));
                           value = None })
                         ]
                  }
                 )) |}]

let%expect_test _ =
  dump {|(a = 5, b = false, c = "foo")|};
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 },
         { Parse.rec' = false;
           fields =
           [(Parse.Decl
               { Parse.kind = None;
                 name_or_count =
                 ({ Starpath.row = 1; col = 2 }, (Parse.Name "a")); type' = None;
                  value = (Some (Parse.Lit (Parse.Num 5))) });
                 (Parse.Decl
                    { Parse.kind = None;
                      name_or_count =
                      ({ Starpath.row = 1; col = 9 }, (Parse.Name "b"));
                       type' = None;
                       value =
                       (Some (Parse.Id (
                                { Starpath.row = 1; col = 13 }, "false"))) });
                       (Parse.Decl
                          { Parse.kind = None;
                            name_or_count =
                            ({ Starpath.row = 1; col = 20 }, (Parse.Name "c"));
                             type' = None;
                             value = (Some (Parse.Lit (Parse.String "foo"))) })
                            ]
                       }
                      )) |}]

let%expect_test _ =
  dump {|(a: int, b: bool, c: string)|};
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 },
         { Parse.rec' = false;
           fields =
           [(Parse.Decl
               { Parse.kind = None;
                 name_or_count =
                 ({ Starpath.row = 1; col = 2 }, (Parse.Name "a"));
                  type' =
                  (Some ({ Starpath.row = 1; col = 5 },
                           (Parse.Id ({ Starpath.row = 1; col = 5 }, "int"))));
                           value = None });
                         (Parse.Decl
                            { Parse.kind = None;
                              name_or_count =
                              ({ Starpath.row = 1; col = 10 }, (Parse.Name "b"));
                               type' =
                               (Some ({ Starpath.row = 1; col = 13 },
                                        (Parse.Id (
                                           { Starpath.row = 1; col = 13 }, "bool"
                                             ))));
                                        value = None });
                                      (Parse.Decl
                                         { Parse.kind = None;
                                           name_or_count =
                                           ({ Starpath.row = 1; col = 19 },
                                              (Parse.Name "c"));
                                            type' =
                                            (Some ({ Starpath.row = 1;
                                                     col = 22 },
                                                     (Parse.Id (
                                                        { Starpath.row = 1;
                                                          col = 22 }, "string"))));
                                                     value = None })
                                                   ]
                                            }
                                           )) |}]

let%expect_test _ =
  dump {|(val a = 5, val b = false, mut c = "foo")|};
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 },
         { Parse.rec' = false;
           fields =
           [(Parse.Decl
               { Parse.kind =
                 (Some ({ Starpath.row = 1; col = 2 }, Parse.Val));
                        name_or_count =
                        ({ Starpath.row = 1; col = 6 }, (Parse.Name "a"));
                         type' = None; value = (Some (Parse.Lit (Parse.Num 5))) });
                        (Parse.Decl
                           { Parse.kind =
                             (Some ({ Starpath.row = 1; col = 13 }, Parse.Val));
                                    name_or_count =
                                    ({ Starpath.row = 1; col = 17 },
                                       (Parse.Name "b"));
                                     type' = None;
                                     value =
                                     (Some (Parse.Id (
                                              { Starpath.row = 1; col = 21 },
                                                "false")))
                                              });
                                     (Parse.Decl
                                        { Parse.kind =
                                          (Some ({ Starpath.row = 1; col = 28 },
                                                   Parse.Mut));
                                                 name_or_count =
                                                 ({ Starpath.row = 1; col = 32 },
                                                    (Parse.Name "c"));
                                                  type' = None;
                                                  value =
                                                  (Some (Parse.Lit
                                                           (Parse.String "foo")))
                                                  })
                                                 ]
                                          }
                                        )) |}]

let%expect_test _ =
  dump {|(val a: int, val b: bool, mut c: string)|};
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 },
         { Parse.rec' = false;
           fields =
           [(Parse.Decl
               { Parse.kind =
                 (Some ({ Starpath.row = 1; col = 2 }, Parse.Val));
                        name_or_count =
                        ({ Starpath.row = 1; col = 6 }, (Parse.Name "a"));
                         type' =
                         (Some ({ Starpath.row = 1; col = 9 },
                                  (Parse.Id (
                                     { Starpath.row = 1; col = 9 }, "int"))));
                                  value = None });
                                (Parse.Decl
                                   { Parse.kind =
                                     (Some ({ Starpath.row = 1; col = 14 },
                                              Parse.Val));
                                            name_or_count =
                                            ({ Starpath.row = 1; col = 18 },
                                               (Parse.Name "b"));
                                             type' =
                                             (Some ({ Starpath.row = 1;
                                                      col = 21 },
                                                      (Parse.Id (
                                                         { Starpath.row = 1;
                                                           col = 21 }, "bool"))));
                                                      value = None });
                                                    (Parse.Decl
                                                       { Parse.kind =
                                                         (Some ({ Starpath.row =
                                                                  1; col = 27 },
                                                                  Parse.Mut));
                                                                name_or_count =
                                                                ({ Starpath.row =
                                                                   1; col = 31 },
                                                                   (Parse.Name
                                                                      "c"));
                                                                 type' =
                                                                 (Some ({ Starpath.row =
                                                                        1;
                                                                        col = 34
                                                                        },
                                                                        (Parse.Id (
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 34
                                                                        },
                                                                        "string"
                                                                        ))));
                                                                        value =
                                                                        None })]
                                                                 }
                                                                )) |}]

let%expect_test _ =
  dump {|(val a: int = 5, val b: bool = false, mut c: string = "foo")|};
  [%expect
    {|
    (Parse.Prod (
       { Starpath.row = 1; col = 1 },
         { Parse.rec' = false;
           fields =
           [(Parse.Decl
               { Parse.kind =
                 (Some ({ Starpath.row = 1; col = 2 }, Parse.Val));
                        name_or_count =
                        ({ Starpath.row = 1; col = 6 }, (Parse.Name "a"));
                         type' =
                         (Some ({ Starpath.row = 1; col = 9 },
                                  (Parse.Id (
                                     { Starpath.row = 1; col = 9 }, "int"))));
                                  value = (Some (Parse.Lit (Parse.Num 5))) });
                                (Parse.Decl
                                   { Parse.kind =
                                     (Some ({ Starpath.row = 1; col = 18 },
                                              Parse.Val));
                                            name_or_count =
                                            ({ Starpath.row = 1; col = 22 },
                                               (Parse.Name "b"));
                                             type' =
                                             (Some ({ Starpath.row = 1;
                                                      col = 25 },
                                                      (Parse.Id (
                                                         { Starpath.row = 1;
                                                           col = 25 }, "bool"))));
                                                      value =
                                                      (Some (Parse.Id (
                                                               { Starpath.row =
                                                                 1; col = 32 },
                                                                 "false")))
                                                               });
                                                      (Parse.Decl
                                                         { Parse.kind =
                                                           (Some ({ Starpath.row =
                                                                    1;
                                                                    col = 39 },
                                                                    Parse.Mut));
                                                                  name_or_count =
                                                                  ({ Starpath.row =
                                                                     1;
                                                                     col = 43 },
                                                                     (Parse.Name
                                                                        "c"));
                                                                   type' =
                                                                   (Some (
                                                                   { Starpath.row =
                                                                     1;
                                                                     col = 46 },
                                                                     (Parse.Id (
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 46
                                                                        },
                                                                        "string"
                                                                        ))));
                                                                     value =
                                                                     (Some (
                                                                     Parse.Lit
                                                                       (Parse.String
                                                                        "foo")))
                                                                     })
                                                                   ] }
                                                                  )) |}]

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
  [%expect
    {|
    (Parse.Block
       [(Parse.Brk
           { Starpath.row = 1; col = 2 });
             (Parse.Ctn { Starpath.row = 1; col = 6 })]) |}]

let%expect_test _ =
  dump
    {|
  # comment
  {
    val i: int = 0 #    another comment
    mut j
    #yet another comment
    loop { }
    ret bool
    j = i
    "yoo"
  }
  |};
  [%expect
    {|
    (Parse.Block
       [(Parse.Decl (
           { Starpath.row = 4; col = 5 },
             { Parse.kind = Parse.Val;
               name =
               ({ Starpath.row = 4; col = 9 }, "i");
                type' =
                (Some (Parse.Id ({ Starpath.row = 4; col = 12 }, "int")));
                         value = (Some (Parse.Lit (Parse.Num 0))) }
                ));
                (Parse.Decl (
                   { Starpath.row = 5; col = 5 },
                     { Parse.kind = Parse.Mut;
                       name =
                       ({ Starpath.row = 5; col = 9 }, "j"); type' = None;
                        value = None }
                       )); (Parse.Loop (Parse.Block []));
                       (Parse.Ret (
                          { Starpath.row = 8; col = 5 },
                            (Some (Parse.Id (
                                     { Starpath.row = 8; col = 9 }, "bool")))));
                                     (Parse.Assign
                                        { Parse.assignee =
                                          (Parse.Id (
                                             { Starpath.row = 9; col = 5 }, "j"));
                                             value =
                                             (Parse.Id (
                                                { Starpath.row = 9; col = 9 },
                                                  "i"))
                                                });
                                             (Parse.Expr
                                                (Parse.Lit (Parse.String "yoo")))
                                             ]) |}]

let%expect_test _ =
  dump "proc()";
  [%expect
    {|
    (Parse.ProcT (
       { Starpath.row = 1; col = 1 },
         { Parse.args =
           ({ Starpath.row = 1; col = 4 }, { Parse.rec' = false; fields = [] });
            return_type = None }
           )) |}]

let%expect_test _ =
  dump "proc(mut a: int = 5, val b: string): int";
  [%expect
    {|
    (Parse.ProcT (
       { Starpath.row = 1; col = 1 },
         { Parse.args =
           ({ Starpath.row = 1; col = 4 },
              { Parse.rec' = false;
                fields =
                [(Parse.Decl
                    { Parse.kind =
                      (Some ({ Starpath.row = 1; col = 6 }, Parse.Mut));
                             name_or_count =
                             ({ Starpath.row = 1; col = 10 }, (Parse.Name "a"));
                              type' =
                              (Some ({ Starpath.row = 1; col = 13 },
                                       (Parse.Id (
                                          { Starpath.row = 1; col = 13 }, "int"))));
                                       value = (Some (Parse.Lit (Parse.Num 5))) });
                                     (Parse.Decl
                                        { Parse.kind =
                                          (Some ({ Starpath.row = 1; col = 22 },
                                                   Parse.Val));
                                                 name_or_count =
                                                 ({ Starpath.row = 1; col = 26 },
                                                    (Parse.Name "b"));
                                                  type' =
                                                  (Some ({ Starpath.row = 1;
                                                           col = 29 },
                                                           (Parse.Id (
                                                              { Starpath.row = 1;
                                                                col = 29 },
                                                                "string"))));
                                                           value = None })
                                                         ]
                                                  });
                                          return_type =
                                          (Some ({ Starpath.row = 1; col = 38 },
                                                   (Parse.Id (
                                                      { Starpath.row = 1;
                                                        col = 38 }, "int"))))
                                                   })) |}]

let%expect_test _ =
  dump "proc() {}";
  [%expect
    {|
    (Parse.Proc
       { Parse.type' =
         { Parse.args =
           ({ Starpath.row = 1; col = 4 }, { Parse.rec' = false; fields = [] });
            return_type = None };
           body = [] }) |}]

let%expect_test _ =
  dump {|
  proc(mut a: int = 5): string { ret "foo" }
  |};
  [%expect
    {|
    (Parse.Proc
       { Parse.type' =
         { Parse.args =
           ({ Starpath.row = 2; col = 6 },
              { Parse.rec' = false;
                fields =
                [(Parse.Decl
                    { Parse.kind =
                      (Some ({ Starpath.row = 2; col = 8 }, Parse.Mut));
                             name_or_count =
                             ({ Starpath.row = 2; col = 12 }, (Parse.Name "a"));
                              type' =
                              (Some ({ Starpath.row = 2; col = 15 },
                                       (Parse.Id (
                                          { Starpath.row = 2; col = 15 }, "int"))));
                                       value = (Some (Parse.Lit (Parse.Num 5))) })
                                     ]
                              });
                      return_type =
                      (Some ({ Starpath.row = 2; col = 25 },
                               (Parse.Id (
                                  { Starpath.row = 2; col = 25 }, "string"))))
                               };
                             body =
                             [(Parse.Ret (
                                 { Starpath.row = 2; col = 34 },
                                   (Some (Parse.Lit (Parse.String "foo")))))]
                               }) |}]

let%expect_test _ =
  dump "{ foo() }";
  [%expect
    {|
    (Parse.Block
       [(Parse.Expr
           (Parse.Call (
              { Starpath.row = 1; col = 3 },
                { Parse.callee =
                  (Parse.Id ({ Starpath.row = 1; col = 3 }, "foo"));
                     args = { Parse.rec' = false; fields = [] } }
                  )))
                ]) |}]

let%expect_test _ =
  dump "foo (a) (b)";
  [%expect
    {|
    (Parse.Call (
       { Starpath.row = 1; col = 1 },
         { Parse.callee =
           (Parse.Call (
              { Starpath.row = 1; col = 1 },
                { Parse.callee =
                  (Parse.Id ({ Starpath.row = 1; col = 1 }, "foo"));
                     args =
                     { Parse.rec' = false;
                       fields =
                       [(Parse.Value (
                           { Starpath.row = 1; col = 6 },
                             (Parse.Id ({ Starpath.row = 1; col = 6 }, "a"))))] }
                         }
                       ));
                     args =
                     { Parse.rec' = false;
                       fields =
                       [(Parse.Value (
                           { Starpath.row = 1; col = 10 },
                             (Parse.Id ({ Starpath.row = 1; col = 10 }, "b"))))]
                             }
                         }
                       )) |}]

let%expect_test _ =
  dump "foo(bar(baz))";
  [%expect
    {|
    (Parse.Call (
       { Starpath.row = 1; col = 1 },
         { Parse.callee =
           (Parse.Id ({ Starpath.row = 1; col = 1 }, "foo"));
              args =
              { Parse.rec' = false;
                fields =
                [(Parse.Value (
                    { Starpath.row = 1; col = 5 },
                      (Parse.Call (
                         { Starpath.row = 1; col = 5 },
                           { Parse.callee =
                             (Parse.Id ({ Starpath.row = 1; col = 5 }, "bar"));
                                args =
                                { Parse.rec' = false;
                                  fields =
                                  [(Parse.Value (
                                      { Starpath.row = 1; col = 9 },
                                        (Parse.Id (
                                           { Starpath.row = 1; col = 9 }, "baz"))
                                             ))
                                           ]
                                        }
                                    }
                                  ))))
                                ]
                             }
                           })) |}]

let%expect_test _ =
  dump "1 + 2 - 3 * 4 / 5 % 6 && 7 || 9 == 10 != 11 < 12 <= 13 . hi";
  [%expect
    {|
    (Parse.Binop (
       { Starpath.row = 1; col = 1 },
         (Parse.Binop (
            { Starpath.row = 1; col = 1 },
              (Parse.Binop (
                 { Starpath.row = 1; col = 1 },
                   (Parse.Binop (
                      { Starpath.row = 1; col = 1 },
                        (Parse.Binop (
                           { Starpath.row = 1; col = 1 },
                             (Parse.Binop (
                                { Starpath.row = 1; col = 1 },
                                  (Parse.Binop (
                                     { Starpath.row = 1; col = 1 },
                                       (Parse.Binop (
                                          { Starpath.row = 1; col = 1 },
                                            (Parse.Binop (
                                               { Starpath.row = 1; col = 1 },
                                                 (Parse.Binop (
                                                    { Starpath.row = 1;
                                                      col = 1 },
                                                      (Parse.Binop (
                                                         { Starpath.row = 1;
                                                           col = 1 },
                                                           (Parse.Lit
                                                              (Parse.Num 1)),
                                                           Parse.Plus,
                                                           { Starpath.row = 1;
                                                             col = 5 },
                                                             (Parse.Lit
                                                                (Parse.Num 2))
                                                             )), Parse.Mins,
                                                             { Starpath.row = 1;
                                                               col = 9 },
                                                               (Parse.Lit
                                                                  (Parse.Num 3))
                                                               )), Parse.Astr,
                                                               { Starpath.row =
                                                                 1; col = 13 },
                                                                 (Parse.Lit
                                                                    (Parse.Num 4))
                                                                 )), Parse.Slsh,
                                                                 { Starpath.row =
                                                                   1; col = 17 },
                                                                   (Parse.Lit
                                                                      (Parse.Num
                                                                        5))
                                                                   )),
                                                                   Parse.Perc,
                                                                   { Starpath.row =
                                                                     1;
                                                                     col = 21 },
                                                                     (Parse.Lit
                                                                        (
                                                                        Parse.Num
                                                                        6))
                                                                     )),
                                                                     Parse.And,
                                                                     { Starpath.row =
                                                                       1;
                                                                       col = 26 },
                                                                       (Parse.Lit
                                                                        (Parse.Num
                                                                        7))
                                                                       )),
                                                                       Parse.Or,
                                                                       { Starpath.row =
                                                                        1;
                                                                        col = 31
                                                                        },
                                                                        (Parse.Lit
                                                                        (Parse.Num
                                                                        9)))),
                                                                        Parse.Eq,
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 36
                                                                        },
                                                                        (Parse.Lit
                                                                        (Parse.Num
                                                                        10)))),
                                                                        Parse.Ne,
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 42
                                                                        },
                                                                        (Parse.Lit
                                                                        (Parse.Num
                                                                        11)))),
                                                                        Parse.Lt,
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 47
                                                                        },
                                                                        (Parse.Lit
                                                                        (Parse.Num
                                                                        12)))),
                                                                        Parse.Le,
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 53
                                                                        },
                                                                        (Parse.Binop (
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 53
                                                                        },
                                                                        (Parse.Lit
                                                                        (Parse.Num
                                                                        13)),
                                                                        Parse.Dot,
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 58
                                                                        },
                                                                        (Parse.Id (
                                                                        { Starpath.row =
                                                                        1;
                                                                        col = 58
                                                                        }, "hi"))
                                                                        )))) |}]

let%expect_test _ =
  dump "-1 + -3";
  [%expect
    {|
    (Parse.Binop (
       { Starpath.row = 1; col = 1 },
         (Parse.Uop (
            { Starpath.row = 1; col = 1 }, Parse.UnaryMins,
              (Parse.Lit (Parse.Num 1)))), Parse.Plus,
              { Starpath.row = 1; col = 6 },
                (Parse.Uop (
                   { Starpath.row = 1; col = 6 }, Parse.UnaryMins,
                     (Parse.Lit (Parse.Num 3)))))) |}]

let%expect_test _ =
  dump "foo(bar).baz";
  [%expect
    {|
    (Parse.Binop (
       { Starpath.row = 1; col = 1 },
         (Parse.Call (
            { Starpath.row = 1; col = 1 },
              { Parse.callee =
                (Parse.Id ({ Starpath.row = 1; col = 1 }, "foo"));
                   args =
                   { Parse.rec' = false;
                     fields =
                     [(Parse.Value (
                         { Starpath.row = 1; col = 5 },
                           (Parse.Id ({ Starpath.row = 1; col = 5 }, "bar"))))] }
                       }
                     )), Parse.Dot,
                     { Starpath.row = 1; col = 10 },
                       (Parse.Id ({ Starpath.row = 1; col = 10 }, "baz"))))|}]
