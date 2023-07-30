let assert_raises = OUnit2.assert_raises

type 'a with_pos = { inner : 'a; pos : Lex.pos } [@@deriving show]
type kind = Pre | Val | Var [@@deriving show]

type stmt =
  | Brk
  | Ctn
  | Ret of expr with_pos option
  | Decl of decl
  | Assign of assign
  | Loop of expr with_pos
  | Expr of expr

and decl = {
  kind : kind with_pos;
  name : string with_pos;
  type_ : expr with_pos option;
  value : expr with_pos option;
}

and assign = { assignee : ident_or_field; value' : expr with_pos }
and ident_or_field = Ident' of string | Field' of field
and field = { accessed : expr; accessor : string with_pos }

and expr =
  | Plus of binop
  | Mins of binop
  | Astr of binop
  | Slsh of binop
  | Perc of binop
  | And of binop
  | Or of binop
  | Not of expr with_pos
  | UnaryMins of expr with_pos
  | Eq of binop
  | Ne of binop
  | Le of binop
  | Lt of binop
  | Sum of sum_variant with_pos list
  | Prod of prod_field with_pos list
  | Ident of string
  | Block of stmt with_pos list
  | If of if_
  | ProcType of proc_type
  | Proc of proc
  | Field of field
  | Call of call
  | Bool of bool
  | Num of int
  | Rune of char
  | String of string
[@@deriving show]

and binop = { lhs : expr; rhs : expr with_pos }

and if_ = {
  cond : expr with_pos;
  if_branch : expr with_pos;
  else_branch : expr with_pos option;
}

and proc_type = {
  args : prod_field with_pos list with_pos;
  return_type : expr with_pos option;
}

and proc = { type_' : proc_type; body : expr with_pos }
and sum_variant = { name' : string; value''' : expr with_pos option }
and ident_or_num = Ident'' of string | Num'' of int
and prod_field = Decl' of decl_field | Value' of expr

and decl_field = {
  kind' : kind option;
  name_or_count : ident_or_num with_pos;
  type_'' : expr with_pos option;
  value'' : expr with_pos option;
}

and call = { callee : expr; args' : prod_field with_pos list with_pos }

type ast = expr with_pos [@@deriving show]
type pos = Lex.pos

(*
Same meaning as UnexpectedEOF but without the pos; gets thrown all over the
place then converted to UnexpectedEOF with pos at the top in parse so that we
don't have to pass around the end_pos everywhere.
*)
exception PreUnexpectedEOF

let expect_advanced tl =
  match tl with
  | [] -> raise PreUnexpectedEOF
  | non_empty -> (List.hd non_empty, List.tl non_empty)

let with_advanced_or tl default f =
  match tl with
  | [] -> default
  | non_empty -> f (List.hd non_empty) (List.tl non_empty)

let rec with_advanced_skipnl_or tl default f =
  match tl with
  | [] -> default
  | non_empty -> (
      let head = List.hd non_empty in
      let tail = List.tl non_empty in
      match head with
      | Lex.Nl, _ -> with_advanced_skipnl_or tail default f
      | _ -> f head tail)

let rec drop_nls = function (Lex.Nl, _) :: xs -> drop_nls xs | o -> o

let try_make_binop t =
  match t with
  | Lex.Plus -> Some (fun lhs rhs -> Plus { lhs; rhs })
  | Mins -> Some (fun lhs rhs -> Mins { lhs; rhs })
  | Astr -> Some (fun lhs rhs -> Astr { lhs; rhs })
  | Slsh -> Some (fun lhs rhs -> Slsh { lhs; rhs })
  | Perc -> Some (fun lhs rhs -> Perc { lhs; rhs })
  | And -> Some (fun lhs rhs -> And { lhs; rhs })
  | Or -> Some (fun lhs rhs -> Or { lhs; rhs })
  | Eq -> Some (fun lhs rhs -> Eq { lhs; rhs })
  | Ne -> Some (fun lhs rhs -> Ne { lhs; rhs })
  | Le -> Some (fun lhs rhs -> Le { lhs; rhs })
  | Lt -> Some (fun lhs rhs -> Lt { lhs; rhs })
  | _ -> None

let kind_from_keywd = function
  | Lex.Pre -> Some Pre
  | Val -> Some Val
  | Var -> Some Val
  | _ -> None

exception UnexpectedToken of Lex.token * pos

let rec parse_expr tl =
  let (t, pos), tl = expect_advanced tl in
  match t with
  | Lex.Ident ident_name ->
      let lhs = Ident ident_name in
      let after_ident_tl = tl in
      with_advanced_or tl
        ({ inner = lhs; pos }, tl)
        (fun (t', sym_pos) tl ->
          match try_make_binop t' with
          | Some make_binop ->
              let rhs, tl = parse_expr tl in
              ({ inner = make_binop lhs rhs; pos }, tl)
          | None -> (
              match t' with
              | Dot -> (
                  let t'', tl = drop_nls tl |> expect_advanced in
                  match t'' with
                  | Ident i, accessor_pos ->
                      ( {
                          inner =
                            Field
                              {
                                accessed = lhs;
                                accessor = { inner = i; pos = accessor_pos };
                              };
                          pos;
                        },
                        tl )
                  | u, pos -> raise (UnexpectedToken (u, pos)))
              | OpenParen ->
                  let args, tl = parse_prod_expr_rest tl in
                  ( {
                      inner =
                        Call
                          {
                            callee = lhs;
                            args' = { inner = args; pos = sym_pos };
                          };
                      pos;
                    },
                    tl )
              | _ -> ({ inner = lhs; pos }, after_ident_tl)))
  | Keywd If -> (
      let cond, tl = parse_expr tl in
      let if_branch, tl = parse_expr tl in
      let after_if_tl = tl in
      match tl with
      | (Keywd Else, _) :: tl ->
          let else_branch, tl = parse_expr tl in
          ( {
              inner = If { cond; if_branch; else_branch = Some else_branch };
              pos;
            },
            tl )
      | _ ->
          ( { inner = If { cond; if_branch; else_branch = None }; pos },
            after_if_tl ))
  | Keywd Proc -> (
      match tl with
      | [] -> raise PreUnexpectedEOF
      | (OpenParen, args_pos) :: tl -> (
          let args, tl = parse_prod_expr_rest tl in
          let after_args_tl = tl in
          match tl with
          | (Lex.Colon, _) :: tl -> (
              let return_type, tl = parse_expr tl in
              match tl with
              | (OpenCurlyBrkt, body_pos) :: tl ->
                  let body_stmts, tl = parse_block_rest tl in
                  ( {
                      inner =
                        Proc
                          {
                            type_' =
                              {
                                args = { inner = args; pos = args_pos };
                                return_type = Some return_type;
                              };
                            body = { inner = Block body_stmts; pos = body_pos };
                          };
                      pos;
                    },
                    tl )
              | _ ->
                  ( {
                      inner =
                        ProcType
                          {
                            args = { inner = args; pos = args_pos };
                            return_type = Some return_type;
                          };
                      pos;
                    },
                    tl ))
          | (OpenCurlyBrkt, body_pos) :: tl ->
              let body_stmts, tl = parse_block_rest tl in
              ( {
                  inner =
                    Proc
                      {
                        type_' =
                          {
                            args = { inner = args; pos = args_pos };
                            return_type = None;
                          };
                        body = { inner = Block body_stmts; pos = body_pos };
                      };
                  pos;
                },
                tl )
          | _ ->
              ( {
                  inner =
                    ProcType
                      {
                        args = { inner = args; pos = args_pos };
                        return_type = None;
                      };
                  pos;
                },
                after_args_tl ))
      | (u, pos) :: _ -> raise (UnexpectedToken (u, pos)))
  | Bool b ->
      let lhs = Bool b in
      let after_bool_tl = tl in
      with_advanced_or tl
        ({ inner = lhs; pos }, tl)
        (fun (t', _) tl ->
          match try_make_binop t' with
          | Some make_binop ->
              let rhs, tl = parse_expr tl in
              ({ inner = make_binop lhs rhs; pos }, tl)
          | None -> ({ inner = lhs; pos }, after_bool_tl))
  | Num n ->
      let lhs = Num n in
      let after_num_tl = tl in
      with_advanced_or tl
        ({ inner = lhs; pos }, tl)
        (fun (t', _) tl ->
          match try_make_binop t' with
          | Some make_binop ->
              let rhs, tl = parse_expr tl in
              ({ inner = make_binop lhs rhs; pos }, tl)
          | None -> ({ inner = lhs; pos }, after_num_tl))
  | String s ->
      let lhs = String s in
      let after_string_tl = tl in
      with_advanced_or tl
        ({ inner = lhs; pos }, tl)
        (fun (t', _) tl ->
          match try_make_binop t' with
          | Some make_binop ->
              let rhs, tl = parse_expr tl in
              ({ inner = make_binop lhs rhs; pos }, tl)
          | None -> ({ inner = lhs; pos }, after_string_tl))
  | Rune c ->
      let lhs = Rune c in
      let after_rune_tl = tl in
      with_advanced_or tl
        ({ inner = lhs; pos }, tl)
        (fun (t', _) tl ->
          match try_make_binop t' with
          | Some make_binop ->
              let rhs, tl = parse_expr tl in
              ({ inner = make_binop lhs rhs; pos }, tl)
          | None -> ({ inner = lhs; pos }, after_rune_tl))
  | Mins ->
      let operand, tl = parse_expr tl in
      ({ inner = UnaryMins operand; pos }, tl)
  | Not ->
      let operand, tl = parse_expr tl in
      ({ inner = Not operand; pos }, tl)
  | OpenParen ->
      let fields, tl = parse_prod_expr_rest tl in
      ({ inner = Prod fields; pos }, tl)
  | OpenSquareBrkt ->
      let variants, tl = parse_sum_expr_rest tl in
      ({ inner = Sum variants; pos }, tl)
  | OpenCurlyBrkt ->
      let stmts, tl = parse_block_rest tl in
      ({ inner = Block stmts; pos }, tl)
  | u -> raise (UnexpectedToken (u, pos))

and parse_prod_expr_rest tl =
  let recurse_with field tl =
    let fields_rest, tl = parse_prod_expr_rest tl in
    (field :: fields_rest, tl)
  in
  let expr_fallback () =
    let { inner; pos }, tl = parse_expr tl in
    let field = { inner = Value' inner; pos } in
    match tl with
    | (Comma, _) :: tl -> recurse_with field tl
    | _ -> recurse_with field tl
  in
  let kind, kind_pos, tl =
    let after_open_paren_tl = tl in
    match tl with
    | [] -> raise PreUnexpectedEOF
    | (Lex.Keywd kw, kind_pos) :: tl -> (
        match kind_from_keywd kw with
        | None -> (None, None, after_open_paren_tl)
        | Some k -> (Some k, Some kind_pos, tl))
    | _ -> (None, None, after_open_paren_tl)
  in
  let proceed ident_or_num field_pos tl =
    let type_, tl =
      let after_maybe_kind_tl = tl in
      match tl with
      | [] -> raise PreUnexpectedEOF
      | (Lex.Colon, _) :: tl ->
          let type_expr, tl = parse_expr tl in
          (Some type_expr, tl)
      | _ -> (None, after_maybe_kind_tl)
    in
    let value, tl =
      let after_maybe_type_tl = tl in
      match tl with
      | [] -> raise PreUnexpectedEOF
      | (Assign, _) :: tl ->
          let value_expr, tl = parse_expr tl in
          (Some value_expr, tl)
      | _ -> (None, after_maybe_type_tl)
    in
    match (tl, kind, type_, value) with
    | [], _, _, _ -> raise PreUnexpectedEOF
    | (Comma, _) :: tl, _, _, _ ->
        recurse_with
          {
            inner =
              Decl'
                {
                  kind' = kind;
                  name_or_count = ident_or_num;
                  type_'' = type_;
                  value'' = value;
                };
            pos = field_pos;
          }
          tl
    | (CloseParen, _) :: _, _, _, _ ->
        recurse_with
          {
            inner =
              Decl'
                {
                  kind' = kind;
                  name_or_count = ident_or_num;
                  type_'' = type_;
                  value'' = value;
                };
            pos = field_pos;
          }
          tl
    | _, None, None, None -> expr_fallback ()
    | (u, pos) :: _, _, _, _ -> raise (UnexpectedToken (u, pos))
  in
  match (tl, kind) with
  | [], _ -> raise PreUnexpectedEOF
  | (Ident ident_name, ident_pos) :: tl, _ ->
      let field_pos = Option.value kind_pos ~default:ident_pos in
      let ident = { inner = Ident'' ident_name; pos = ident_pos } in
      proceed ident field_pos tl
  | (Num n, num_pos) :: tl, _ ->
      let field_pos = Option.value kind_pos ~default:num_pos in
      let ident = { inner = Num'' n; pos = num_pos } in
      proceed ident field_pos tl
  | (Nl, _) :: tl, None -> parse_prod_expr_rest tl
  | (CloseParen, _) :: tl, None -> ([], tl)
  | _, None -> expr_fallback ()
  | (u, pos) :: _, Some _ -> raise (UnexpectedToken (u, pos))

and parse_sum_expr_rest = function
  | [] -> raise PreUnexpectedEOF
  | (Ident name', pos) :: tl ->
      let variant, tl =
        match tl with
        | [] -> raise PreUnexpectedEOF
        | (OpenParen, _) :: tl -> (
            let value_type, tl = parse_expr tl in
            match tl with
            | [] -> raise PreUnexpectedEOF
            | (CloseParen, _) :: tl -> (
                match tl with
                | [] -> raise PreUnexpectedEOF
                | (Comma, _) :: tl ->
                    ({ inner = { name'; value''' = Some value_type }; pos }, tl)
                | (CloseSquareBrkt, _) :: _ ->
                    ({ inner = { name'; value''' = Some value_type }; pos }, tl)
                | (u, pos) :: _ -> raise (UnexpectedToken (u, pos)))
            | (u, pos) :: _ -> raise (UnexpectedToken (u, pos)))
        | (Comma, _) :: tl -> ({ inner = { name'; value''' = None }; pos }, tl)
        | (CloseSquareBrkt, _) :: _ ->
            ({ inner = { name'; value''' = None }; pos }, tl)
        | (u, pos) :: _ -> raise (UnexpectedToken (u, pos))
      in
      let variants_rest, tl = parse_sum_expr_rest tl in
      (variant :: variants_rest, tl)
  | (Nl, _) :: tl -> parse_sum_expr_rest tl
  | (CloseSquareBrkt, _) :: tl -> ([], tl)
  | (u, pos) :: _ -> raise (UnexpectedToken (u, pos))

and parse_block_rest tl =
  let stmt, tl = parse_stmt tl in
  let stmts_rest, tl = parse_block_after_first_stmt tl in
  (stmt :: stmts_rest, tl)

and parse_block_after_first_stmt = function
  | [] -> raise PreUnexpectedEOF
  | (Lex.Nl, _) :: tl -> parse_block_after_first_stmt tl
  | (CloseCurlyBrkt, _) :: tl -> ([], tl)
  | tl ->
      let stmt, tl = parse_stmt tl in
      let stmts_rest, tl = parse_block_after_first_stmt tl in
      (stmt :: stmts_rest, tl)

(*
All exprs are stmts, but not all stmts are exprs. parse_stmt tries to parse
things as a stmt first, but if that fails then just gives up and calls
parse_expr and wraps it in the Expr constructor.
*)

and parse_stmt tl =
  let expr_fallback () =
    let { inner; pos }, tl = parse_expr tl in
    ({ inner = Expr inner; pos }, tl)
  in
  let (t, pos), tl = expect_advanced tl in
  match t with
  | Lex.Ident ident_name -> (
      match tl with
      (* field assignee *)
      | (Assign, _) :: tl ->
          let value', tl = parse_expr tl in
          ({ inner = Assign { assignee = Ident' ident_name; value' }; pos }, tl)
      | _ -> expr_fallback ())
  | Keywd Brk -> (
      match tl with
      | [] -> ({ inner = Brk; pos }, tl)
      | (Nl, _) :: tl -> ({ inner = Brk; pos }, tl)
      | (CloseCurlyBrkt, _) :: _ -> ({ inner = Brk; pos }, tl)
      | (u, pos) :: _ -> raise (UnexpectedToken (u, pos)))
  | Keywd Ctn -> (
      match tl with
      | [] -> ({ inner = Ctn; pos }, tl)
      | (Nl, _) :: tl -> ({ inner = Ctn; pos }, tl)
      | (CloseCurlyBrkt, _) :: _ -> ({ inner = Ctn; pos }, tl)
      | (u, pos) :: _ -> raise (UnexpectedToken (u, pos)))
  | Keywd Ret -> (
      match tl with
      | [] -> ({ inner = Ret None; pos }, tl)
      | (Nl, _) :: tl -> ({ inner = Ret None; pos }, tl)
      | (CloseCurlyBrkt, _) :: _ -> ({ inner = Ret None; pos }, tl)
      | _ ->
          let expr, tl = parse_expr tl in
          ({ inner = Ret (Some expr); pos }, tl))
  | Keywd Loop ->
      let expr, tl = parse_expr tl in
      ({ inner = Loop expr; pos }, tl)
  | Keywd kw -> (
      match kind_from_keywd kw with
      | None -> expr_fallback ()
      | Some kind_inner -> (
          let kind = { inner = kind_inner; pos } in
          match tl with
          | [] -> raise PreUnexpectedEOF
          | (Ident name_string, ident_pos) :: tl -> (
              let name = { inner = name_string; pos = ident_pos } in
              let after_ident_tl = tl in
              match tl with
              | [] -> raise PreUnexpectedEOF
              | (Colon, _) :: tl -> (
                  let type_, tl = parse_expr tl in
                  let after_type_tl = tl in
                  match tl with
                  | [] -> raise PreUnexpectedEOF
                  | (Assign, _) :: tl ->
                      let value, tl = parse_expr tl in
                      ( {
                          inner =
                            Decl
                              {
                                kind;
                                name;
                                type_ = Some type_;
                                value = Some value;
                              };
                          pos;
                        },
                        tl )
                  | (Nl, _) :: tl ->
                      ( {
                          inner =
                            Decl
                              { kind; name; type_ = Some type_; value = None };
                          pos;
                        },
                        tl )
                  | (CloseCurlyBrkt, _) :: _ ->
                      ( {
                          inner =
                            Decl
                              { kind; name; type_ = Some type_; value = None };
                          pos;
                        },
                        after_type_tl )
                  | (u, pos) :: _ -> raise (UnexpectedToken (u, pos)))
              | (Assign, _) :: tl ->
                  let value, tl = parse_expr tl in
                  ( {
                      inner =
                        Decl { kind; name; type_ = None; value = Some value };
                      pos;
                    },
                    tl )
              | (Nl, _) :: tl ->
                  ( {
                      inner = Decl { kind; name; type_ = None; value = None };
                      pos;
                    },
                    tl )
              | (CloseCurlyBrkt, _) :: _ ->
                  ( {
                      inner = Decl { kind; name; type_ = None; value = None };
                      pos;
                    },
                    after_ident_tl )
              | (u, pos) :: _ -> raise (UnexpectedToken (u, pos)))
          | (u, pos) :: _ -> raise (UnexpectedToken (u, pos))))
  | Nl -> parse_stmt tl
  | _ -> expr_fallback ()

exception UnexpectedEOF of pos

let parse text =
  let lr = Lex.lex text in
  try
    let ast, trailing = drop_nls lr.tokens |> parse_expr in
    with_advanced_skipnl_or trailing ast (fun (t, pos) _ ->
        raise (UnexpectedToken (t, pos)))
  with PreUnexpectedEOF -> raise (UnexpectedEOF lr.end_pos)

let%expect_test _ =
  parse "true" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Bool true); pos = 1:1 } |}]

let%expect_test _ =
  parse "false" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Bool false); pos = 1:1 } |}]

let%expect_test _ =
  parse "0" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Num 0); pos = 1:1 } |}]

let%expect_test _ =
  parse "35185" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Num 35185); pos = 1:1 } |}]

let%expect_test _ =
  parse "0123456789" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Num 123456789); pos = 1:1 } |}]

let%expect_test _ =
  parse "\"foo bar baz\"" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.String "foo bar baz"); pos = 1:1 } |}]

let%expect_test _ =
  parse "'\\n'" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Rune '\n'); pos = 1:1 } |}]

let%test_unit _ =
  let f () = parse "=" in
  assert_raises (UnexpectedToken (Assign, { row = 1; col = 1 })) f

let%test_unit _ =
  let f () = parse "<=" in
  assert_raises (UnexpectedToken (Le, { row = 1; col = 1 })) f

let%test_unit _ =
  let f () = parse ":" in
  assert_raises (UnexpectedToken (Colon, { row = 1; col = 1 })) f

let%test_unit _ =
  let f () = parse "\n\n  " in
  assert_raises (UnexpectedEOF { row = 3; col = 3 }) f

let%expect_test _ =
  parse "true || false" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Or
         { Parse.lhs = (Parse.Bool true);
           rhs = { Parse.inner = (Parse.Bool false); pos = 1:9 } });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "foo % bar" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Perc
         { Parse.lhs = (Parse.Ident "foo");
           rhs = { Parse.inner = (Parse.Ident "bar"); pos = 1:7 } });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "1 + 2 - 3 * 4 / 5 % 6 && 7 || 8 == 9 != 10 <= 11 < 12"
  |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Plus
         { Parse.lhs = (Parse.Num 1);
           rhs =
           { Parse.inner =
             (Parse.Mins
                { Parse.lhs = (Parse.Num 2);
                  rhs =
                  { Parse.inner =
                    (Parse.Astr
                       { Parse.lhs = (Parse.Num 3);
                         rhs =
                         { Parse.inner =
                           (Parse.Slsh
                              { Parse.lhs = (Parse.Num 4);
                                rhs =
                                { Parse.inner =
                                  (Parse.Perc
                                     { Parse.lhs = (Parse.Num 5);
                                       rhs =
                                       { Parse.inner =
                                         (Parse.And
                                            { Parse.lhs = (Parse.Num 6);
                                              rhs =
                                              { Parse.inner =
                                                (Parse.Or
                                                   { Parse.lhs = (Parse.Num 7);
                                                     rhs =
                                                     { Parse.inner =
                                                       (Parse.Eq
                                                          { Parse.lhs =
                                                            (Parse.Num 8);
                                                            rhs =
                                                            { Parse.inner =
                                                              (Parse.Ne
                                                                 { Parse.lhs =
                                                                   (Parse.Num 9);
                                                                   rhs =
                                                                   { Parse.inner =
                                                                     (Parse.Le
                                                                        { Parse.lhs =
                                                                        (Parse.Num
                                                                        10);
                                                                        rhs =
                                                                        { Parse.inner =
                                                                        (Parse.Lt
                                                                        { Parse.lhs =
                                                                        (Parse.Num
                                                                        11);
                                                                        rhs =
                                                                        { Parse.inner =
                                                                        (Parse.Num
                                                                        12);
                                                                        pos =
                                                                        1:52 } });
                                                                        pos =
                                                                        1:47 } });
                                                                     pos = 1:41 }
                                                                   });
                                                              pos = 1:36 }
                                                            });
                                                       pos = 1:31 }
                                                     });
                                                pos = 1:26 }
                                              });
                                         pos = 1:21 }
                                       });
                                  pos = 1:17 }
                                });
                           pos = 1:13 }
                         });
                    pos = 1:9 }
                  });
             pos = 1:5 }
           });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "\"foo\" + \"bar\"" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Plus
         { Parse.lhs = (Parse.String "foo");
           rhs = { Parse.inner = (Parse.String "bar"); pos = 1:9 } });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "'f' / 'b'" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Slsh
         { Parse.lhs = (Parse.Rune 'f');
           rhs = { Parse.inner = (Parse.Rune 'b'); pos = 1:7 } });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "{ 'f' }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block [{ Parse.inner = (Parse.Expr (Parse.Rune 'f')); pos = 1:3 }]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "-77" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner = (Parse.UnaryMins { Parse.inner = (Parse.Num 77); pos = 1:2 });
      pos = 1:1 } |}]

let%expect_test _ =
  parse "-77 - -77" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.UnaryMins
         { Parse.inner =
           (Parse.Mins
              { Parse.lhs = (Parse.Num 77);
                rhs =
                { Parse.inner =
                  (Parse.UnaryMins { Parse.inner = (Parse.Num 77); pos = 1:8 });
                  pos = 1:7 }
                });
           pos = 1:2 });
      pos = 1:1 } |}]

let%expect_test _ =
  parse "!false" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner = (Parse.Not { Parse.inner = (Parse.Bool false); pos = 1:2 });
      pos = 1:1 } |}]

let%test_unit _ =
  let f () = parse "5 5" in
  assert_raises (UnexpectedToken (Num 5, { row = 1; col = 3 })) f

let%expect_test _ =
  parse "if true false" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.If
         { Parse.cond = { Parse.inner = (Parse.Bool true); pos = 1:4 };
           if_branch = { Parse.inner = (Parse.Bool false); pos = 1:9 };
           else_branch = None });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "if true false else true" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.If
         { Parse.cond = { Parse.inner = (Parse.Bool true); pos = 1:4 };
           if_branch = { Parse.inner = (Parse.Bool false); pos = 1:9 };
           else_branch = (Some { Parse.inner = (Parse.Bool true); pos = 1:20 }) });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "if true { i = 1 } else { i = 2 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.If
         { Parse.cond = { Parse.inner = (Parse.Bool true); pos = 1:4 };
           if_branch =
           { Parse.inner =
             (Parse.Block
                [{ Parse.inner =
                   (Parse.Assign
                      { Parse.assignee = (Parse.Ident' "i");
                        value' = { Parse.inner = (Parse.Num 1); pos = 1:15 } });
                   pos = 1:11 }
                  ]);
             pos = 1:9 };
           else_branch =
           (Some { Parse.inner =
                   (Parse.Block
                      [{ Parse.inner =
                         (Parse.Assign
                            { Parse.assignee = (Parse.Ident' "i");
                              value' =
                              { Parse.inner = (Parse.Num 2); pos = 1:30 } });
                         pos = 1:26 }
                        ]);
                   pos = 1:24 })
           });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "if true { i = 1 } else if false { i = 2 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.If
         { Parse.cond = { Parse.inner = (Parse.Bool true); pos = 1:4 };
           if_branch =
           { Parse.inner =
             (Parse.Block
                [{ Parse.inner =
                   (Parse.Assign
                      { Parse.assignee = (Parse.Ident' "i");
                        value' = { Parse.inner = (Parse.Num 1); pos = 1:15 } });
                   pos = 1:11 }
                  ]);
             pos = 1:9 };
           else_branch =
           (Some { Parse.inner =
                   (Parse.If
                      { Parse.cond =
                        { Parse.inner = (Parse.Bool false); pos = 1:27 };
                        if_branch =
                        { Parse.inner =
                          (Parse.Block
                             [{ Parse.inner =
                                (Parse.Assign
                                   { Parse.assignee = (Parse.Ident' "i");
                                     value' =
                                     { Parse.inner = (Parse.Num 2); pos = 1:39 }
                                     });
                                pos = 1:35 }
                               ]);
                          pos = 1:33 };
                        else_branch = None });
                   pos = 1:24 })
           });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "if true { i = 1 } else if false { i = 2 } else { i = 3 }"
  |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.If
         { Parse.cond = { Parse.inner = (Parse.Bool true); pos = 1:4 };
           if_branch =
           { Parse.inner =
             (Parse.Block
                [{ Parse.inner =
                   (Parse.Assign
                      { Parse.assignee = (Parse.Ident' "i");
                        value' = { Parse.inner = (Parse.Num 1); pos = 1:15 } });
                   pos = 1:11 }
                  ]);
             pos = 1:9 };
           else_branch =
           (Some { Parse.inner =
                   (Parse.If
                      { Parse.cond =
                        { Parse.inner = (Parse.Bool false); pos = 1:27 };
                        if_branch =
                        { Parse.inner =
                          (Parse.Block
                             [{ Parse.inner =
                                (Parse.Assign
                                   { Parse.assignee = (Parse.Ident' "i");
                                     value' =
                                     { Parse.inner = (Parse.Num 2); pos = 1:39 }
                                     });
                                pos = 1:35 }
                               ]);
                          pos = 1:33 };
                        else_branch =
                        (Some { Parse.inner =
                                (Parse.Block
                                   [{ Parse.inner =
                                      (Parse.Assign
                                         { Parse.assignee = (Parse.Ident' "i");
                                           value' =
                                           { Parse.inner = (Parse.Num 3);
                                             pos = 1:54 }
                                           });
                                      pos = 1:50 }
                                     ]);
                                pos = 1:48 })
                        });
                   pos = 1:24 })
           });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "{ true }    " |> show_ast |> print_endline;
  [%expect
    {|
      { Parse.inner =
        (Parse.Block [{ Parse.inner = (Parse.Expr (Parse.Bool true)); pos = 1:3 }]);
        pos = 1:1 } |}]

let%test_unit _ =
  let f () = parse "{ true   " in
  assert_raises (UnexpectedEOF { row = 1; col = 10 }) f

let%expect_test _ =
  parse "{ brk }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner = (Parse.Block [{ Parse.inner = Parse.Brk; pos = 1:3 }]);
      pos = 1:1 }
  |}]

let%test_unit _ =
  let f () = parse "{ brk" in
  assert_raises (UnexpectedEOF { row = 1; col = 6 }) f

let%test_unit _ =
  let f () = parse "{ brk." in
  assert_raises (UnexpectedToken (Dot, { row = 1; col = 6 })) f

let%expect_test _ =
  parse "{ ctn }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner = (Parse.Block [{ Parse.inner = Parse.Ctn; pos = 1:3 }]);
      pos = 1:1 }
  |}]

let%test_unit _ =
  let f () = parse "{ ctn" in
  assert_raises (UnexpectedEOF { row = 1; col = 6 }) f

let%test_unit _ =
  let f () = parse "{ ctn." in
  assert_raises (UnexpectedToken (Dot, { row = 1; col = 6 })) f

let%expect_test _ =
  parse "{ ret }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner = (Parse.Block [{ Parse.inner = (Parse.Ret None); pos = 1:3 }]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "{ ret 5 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner =
            (Parse.Ret (Some { Parse.inner = (Parse.Num 5); pos = 1:7 }));
            pos = 1:3 }
           ]);
      pos = 1:1 }
  |}]

let%test_unit _ =
  let f () = parse "{ ret" in
  assert_raises (UnexpectedEOF { row = 1; col = 6 }) f

let%test_unit _ =
  let f () = parse "{ ret." in
  assert_raises (UnexpectedToken (Dot, { row = 1; col = 6 })) f

let%expect_test _ =
  parse {|
    {
      ret
    }
  |} |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner = (Parse.Block [{ Parse.inner = (Parse.Ret None); pos = 3:7 }]);
      pos = 2:5 }
  |}]

let%expect_test _ =
  parse "{ brk\nctn\nret }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner = Parse.Brk; pos = 1:3 };
           { Parse.inner = Parse.Ctn; pos = 2:1 };
           { Parse.inner = (Parse.Ret None); pos = 3:1 }]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "{ loop 5 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner = (Parse.Loop { Parse.inner = (Parse.Num 5); pos = 1:8 });
            pos = 1:3 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse {|
  {
    loop {
      i = i + 1
    }
  }
  |}
  |> show_ast |> print_endline;
  [%expect
    {|
      { Parse.inner =
        (Parse.Block
           [{ Parse.inner =
              (Parse.Loop
                 { Parse.inner =
                   (Parse.Block
                      [{ Parse.inner =
                         (Parse.Assign
                            { Parse.assignee = (Parse.Ident' "i");
                              value' =
                              { Parse.inner =
                                (Parse.Plus
                                   { Parse.lhs = (Parse.Ident "i");
                                     rhs =
                                     { Parse.inner = (Parse.Num 1); pos = 4:15 } });
                                pos = 4:11 }
                              });
                         pos = 4:7 }
                        ]);
                   pos = 3:10 });
              pos = 3:5 }
             ]);
        pos = 2:3 }
  |}]

let%expect_test _ =
  parse "{ pre foo }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner =
            (Parse.Decl
               { Parse.kind = { Parse.inner = Parse.Pre; pos = 1:3 };
                 name = { Parse.inner = "foo"; pos = 1:7 }; type_ = None;
                 value = None });
            pos = 1:3 }
           ]);
      pos = 1:1 }
  |}]

let%test_unit _ =
  let f () = parse "{ pre" in
  assert_raises (UnexpectedEOF { row = 1; col = 6 }) f

let%test_unit _ =
  let f () = parse "{ pre." in
  assert_raises (UnexpectedToken (Dot, { row = 1; col = 6 })) f

let%expect_test _ =
  parse {|
    {
      val foo
    }
  |} |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner =
            (Parse.Decl
               { Parse.kind = { Parse.inner = Parse.Val; pos = 3:7 };
                 name = { Parse.inner = "foo"; pos = 3:11 }; type_ = None;
                 value = None });
            pos = 3:7 }
           ]);
      pos = 2:5 }
  |}]

let%test_unit _ =
  let f () = parse "{ val foo" in
  assert_raises (UnexpectedEOF { row = 1; col = 10 }) f

let%test_unit _ =
  let f () = parse "{ val foo ." in
  assert_raises (UnexpectedToken (Dot, { row = 1; col = 11 })) f

let%test_unit _ =
  let f () = parse "{ var foo: Bar" in
  assert_raises (UnexpectedEOF { row = 1; col = 15 }) f

let%expect_test _ =
  parse {|
    {
      var foo: Nat
    }
  |} |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner =
            (Parse.Decl
               { Parse.kind = { Parse.inner = Parse.Val; pos = 3:7 };
                 name = { Parse.inner = "foo"; pos = 3:11 };
                 type_ = (Some { Parse.inner = (Parse.Ident "Nat"); pos = 3:16 });
                 value = None });
            pos = 3:7 }
           ]);
      pos = 2:5 }
  |}]

let%test_unit _ =
  let f () = parse "{ var foo: Bar)" in
  assert_raises (UnexpectedToken (CloseParen, { row = 1; col = 15 })) f

let%expect_test _ =
  parse "{ foo + 9 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner =
            (Parse.Expr
               (Parse.Plus
                  { Parse.lhs = (Parse.Ident "foo");
                    rhs = { Parse.inner = (Parse.Num 9); pos = 1:9 } }));
            pos = 1:3 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "{ val bar: 7 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner =
            (Parse.Decl
               { Parse.kind = { Parse.inner = Parse.Val; pos = 1:3 };
                 name = { Parse.inner = "bar"; pos = 1:7 };
                 type_ = (Some { Parse.inner = (Parse.Num 7); pos = 1:12 });
                 value = None });
            pos = 1:3 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "{ var bar = 7 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner =
            (Parse.Decl
               { Parse.kind = { Parse.inner = Parse.Val; pos = 1:3 };
                 name = { Parse.inner = "bar"; pos = 1:7 }; type_ = None;
                 value = (Some { Parse.inner = (Parse.Num 7); pos = 1:13 }) });
            pos = 1:3 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse {|
  {
    val bar: Nat = 9

    pre baz: Nat = 9

  }
  |}
  |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Block
         [{ Parse.inner =
            (Parse.Decl
               { Parse.kind = { Parse.inner = Parse.Val; pos = 3:5 };
                 name = { Parse.inner = "bar"; pos = 3:9 };
                 type_ = (Some { Parse.inner = (Parse.Ident "Nat"); pos = 3:14 });
                 value = (Some { Parse.inner = (Parse.Num 9); pos = 3:20 }) });
            pos = 3:5 };
           { Parse.inner =
             (Parse.Decl
                { Parse.kind = { Parse.inner = Parse.Pre; pos = 5:5 };
                  name = { Parse.inner = "baz"; pos = 5:9 };
                  type_ =
                  (Some { Parse.inner = (Parse.Ident "Nat"); pos = 5:14 });
                  value = (Some { Parse.inner = (Parse.Num 9); pos = 5:20 }) });
             pos = 5:5 }
           ]);
      pos = 2:3 }
  |}]

let%expect_test _ =
  parse "[]" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Sum []); pos = 1:1 } |}]

let%expect_test _ =
  parse "[\n\n\n]" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Sum []); pos = 1:1 } |}]

let%test_unit _ =
  let f () = parse "[" in
  assert_raises (UnexpectedEOF { row = 1; col = 2 }) f

let%test_unit _ =
  let f () = parse "[." in
  assert_raises (UnexpectedToken (Dot, { row = 1; col = 2 })) f

let%test_unit _ =
  let f () = parse "[Red" in
  assert_raises (UnexpectedEOF { row = 1; col = 5 }) f

let%test_unit _ =
  let f () = parse "[Green(Foo" in
  assert_raises (UnexpectedEOF { row = 1; col = 11 }) f

let%test_unit _ =
  let f () = parse "[Blue(Foo)" in
  assert_raises (UnexpectedEOF { row = 1; col = 11 }) f

let%test_unit _ =
  let f () = parse "[Blue(Foo)." in
  assert_raises (UnexpectedToken (Dot, { row = 1; col = 11 })) f

let%test_unit _ =
  let f () = parse "[Blue(Foo]" in
  assert_raises (UnexpectedToken (CloseSquareBrkt, { row = 1; col = 10 })) f

let%test_unit _ =
  let f () = parse "[Red." in
  assert_raises (UnexpectedToken (Dot, { row = 1; col = 5 })) f

let%expect_test _ =
  parse "[Red, Green, Blue]" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Sum
         [{ Parse.inner = { Parse.name' = "Red"; value''' = None }; pos = 1:2 };
           { Parse.inner = { Parse.name' = "Green"; value''' = None }; pos = 1:7
             };
           { Parse.inner = { Parse.name' = "Blue"; value''' = None }; pos = 1:14
             }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "[Red,\n\nGreen, Blue,]" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Sum
         [{ Parse.inner = { Parse.name' = "Red"; value''' = None }; pos = 1:2 };
           { Parse.inner = { Parse.name' = "Green"; value''' = None }; pos = 3:1
             };
           { Parse.inner = { Parse.name' = "Blue"; value''' = None }; pos = 3:8 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse {|
    [
      Red(Nat8),
      Green,
      Blue,
    ]
  |}
  |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Sum
         [{ Parse.inner =
            { Parse.name' = "Red";
              value''' =
              (Some { Parse.inner = (Parse.Ident "Nat8"); pos = 3:11 }) };
            pos = 3:7 };
           { Parse.inner = { Parse.name' = "Green"; value''' = None }; pos = 4:7
             };
           { Parse.inner = { Parse.name' = "Blue"; value''' = None }; pos = 5:7 }
           ]);
      pos = 2:5 }
  |}]

let%expect_test _ =
  parse "[Blue(void)]" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Sum
         [{ Parse.inner =
            { Parse.name' = "Blue";
              value''' = (Some { Parse.inner = (Parse.Ident "void"); pos = 1:7 })
              };
            pos = 1:2 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "()" |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Prod []); pos = 1:1 } |}]

let%test_unit _ =
  let f () = parse "(val" in
  assert_raises (UnexpectedEOF { row = 1; col = 5 }) f

let%test_unit _ =
  let f () = parse "(pre ]" in
  assert_raises (UnexpectedToken (CloseSquareBrkt, { row = 1; col = 6 })) f

let%expect_test _ =
  parse {|(

  )
|} |> show_ast |> print_endline;
  [%expect {| { Parse.inner = (Parse.Prod []); pos = 1:1 } |}]

let%expect_test _ =
  parse "(37)" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Prod
         [{ Parse.inner =
            (Parse.Decl'
               { Parse.kind' = None;
                 name_or_count = { Parse.inner = (Parse.Num'' 37); pos = 1:2 };
                 type_'' = None; value'' = None });
            pos = 1:2 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "(37,)" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Prod
         [{ Parse.inner =
            (Parse.Decl'
               { Parse.kind' = None;
                 name_or_count = { Parse.inner = (Parse.Num'' 37); pos = 1:2 };
                 type_'' = None; value'' = None });
            pos = 1:2 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse {|(
    37,
  )
|} |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Prod
         [{ Parse.inner =
            (Parse.Decl'
               { Parse.kind' = None;
                 name_or_count = { Parse.inner = (Parse.Num'' 37); pos = 2:5 };
                 type_'' = None; value'' = None });
            pos = 2:5 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "(37: Bool,)" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Prod
         [{ Parse.inner =
            (Parse.Decl'
               { Parse.kind' = None;
                 name_or_count = { Parse.inner = (Parse.Num'' 37); pos = 1:2 };
                 type_'' =
                 (Some { Parse.inner = (Parse.Ident "Bool"); pos = 1:6 });
                 value'' = None });
            pos = 1:2 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "(37 * 88)" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Prod
         [{ Parse.inner =
            (Parse.Value'
               (Parse.Astr
                  { Parse.lhs = (Parse.Num 37);
                    rhs = { Parse.inner = (Parse.Num 88); pos = 1:7 } }));
            pos = 1:2 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "(37 * 88, 'o', foo)" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Prod
         [{ Parse.inner =
            (Parse.Value'
               (Parse.Astr
                  { Parse.lhs = (Parse.Num 37);
                    rhs = { Parse.inner = (Parse.Num 88); pos = 1:7 } }));
            pos = 1:2 };
           { Parse.inner = (Parse.Value' (Parse.Rune 'o')); pos = 1:11 };
           { Parse.inner =
             (Parse.Decl'
                { Parse.kind' = None;
                  name_or_count =
                  { Parse.inner = (Parse.Ident'' "foo"); pos = 1:16 };
                  type_'' = None; value'' = None });
             pos = 1:16 }
           ]);
      pos = 1:1 } |}]

let%expect_test _ =
  parse "(pre foo, pre bar, pre baz)" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Prod
         [{ Parse.inner =
            (Parse.Decl'
               { Parse.kind' = (Some Parse.Pre);
                 name_or_count =
                 { Parse.inner = (Parse.Ident'' "foo"); pos = 1:6 };
                 type_'' = None; value'' = None });
            pos = 1:2 };
           { Parse.inner =
             (Parse.Decl'
                { Parse.kind' = (Some Parse.Pre);
                  name_or_count =
                  { Parse.inner = (Parse.Ident'' "bar"); pos = 1:15 };
                  type_'' = None; value'' = None });
             pos = 1:11 };
           { Parse.inner =
             (Parse.Decl'
                { Parse.kind' = (Some Parse.Pre);
                  name_or_count =
                  { Parse.inner = (Parse.Ident'' "baz"); pos = 1:24 };
                  type_'' = None; value'' = None });
             pos = 1:20 }
           ]);
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "(pre foo: Nat = 7, val bar: Bool = false, var baz: Str = \"baz\",)"
  |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Prod
         [{ Parse.inner =
            (Parse.Decl'
               { Parse.kind' = (Some Parse.Pre);
                 name_or_count =
                 { Parse.inner = (Parse.Ident'' "foo"); pos = 1:6 };
                 type_'' =
                 (Some { Parse.inner = (Parse.Ident "Nat"); pos = 1:11 });
                 value'' = (Some { Parse.inner = (Parse.Num 7); pos = 1:17 }) });
            pos = 1:2 };
           { Parse.inner =
             (Parse.Decl'
                { Parse.kind' = (Some Parse.Val);
                  name_or_count =
                  { Parse.inner = (Parse.Ident'' "bar"); pos = 1:24 };
                  type_'' =
                  (Some { Parse.inner = (Parse.Ident "Bool"); pos = 1:29 });
                  value'' =
                  (Some { Parse.inner = (Parse.Bool false); pos = 1:36 }) });
             pos = 1:20 };
           { Parse.inner =
             (Parse.Decl'
                { Parse.kind' = (Some Parse.Val);
                  name_or_count =
                  { Parse.inner = (Parse.Ident'' "baz"); pos = 1:47 };
                  type_'' =
                  (Some { Parse.inner = (Parse.Ident "Str"); pos = 1:52 });
                  value'' =
                  (Some { Parse.inner = (Parse.String "baz"); pos = 1:58 }) });
             pos = 1:43 }
           ]);
      pos = 1:1 }
  |}]

let%test_unit _ =
  let f () = parse "proc" in
  assert_raises (UnexpectedEOF { row = 1; col = 5 }) f

let%test_unit _ =
  let f () = parse "proc*" in
  assert_raises (UnexpectedToken (Astr, { row = 1; col = 5 })) f

let%expect_test _ =
  parse "proc()" |> show_ast |> print_endline;
  [%expect
    {|
      { Parse.inner =
        (Parse.ProcType
           { Parse.args = { Parse.inner = []; pos = 1:5 }; return_type = None });
        pos = 1:1 } |}]

let%expect_test _ =
  parse "proc(): Nat" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.ProcType
         { Parse.args = { Parse.inner = []; pos = 1:5 };
           return_type = (Some { Parse.inner = (Parse.Ident "Nat"); pos = 1:9 })
           });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "proc() { () }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Proc
         { Parse.type_' =
           { Parse.args = { Parse.inner = []; pos = 1:5 }; return_type = None };
           body =
           { Parse.inner =
             (Parse.Block
                [{ Parse.inner = (Parse.Expr (Parse.Prod [])); pos = 1:10 }]);
             pos = 1:8 }
           });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "proc(): Nat { 1 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Proc
         { Parse.type_' =
           { Parse.args = { Parse.inner = []; pos = 1:5 };
             return_type =
             (Some { Parse.inner = (Parse.Ident "Nat"); pos = 1:9 }) };
           body =
           { Parse.inner =
             (Parse.Block
                [{ Parse.inner = (Parse.Expr (Parse.Num 1)); pos = 1:15 }]);
             pos = 1:13 }
           });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "proc(): { if false Nat else Int } { 1 }" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Proc
         { Parse.type_' =
           { Parse.args = { Parse.inner = []; pos = 1:5 };
             return_type =
             (Some { Parse.inner =
                     (Parse.Block
                        [{ Parse.inner =
                           (Parse.Expr
                              (Parse.If
                                 { Parse.cond =
                                   { Parse.inner = (Parse.Bool false); pos = 1:14
                                     };
                                   if_branch =
                                   { Parse.inner = (Parse.Ident "Nat");
                                     pos = 1:20 };
                                   else_branch =
                                   (Some { Parse.inner = (Parse.Ident "Int");
                                           pos = 1:29 })
                                   }));
                           pos = 1:11 }
                          ]);
                     pos = 1:9 })
             };
           body =
           { Parse.inner =
             (Parse.Block
                [{ Parse.inner = (Parse.Expr (Parse.Num 1)); pos = 1:37 }]);
             pos = 1:35 }
           });
      pos = 1:1 }
  |}]

let%expect_test _ =
  parse "foo.bar" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Field
         { Parse.accessed = (Parse.Ident "foo");
           accessor = { Parse.inner = "bar"; pos = 1:5 } });
      pos = 1:1 } |}]

let%expect_test _ =
  parse "foo()" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Call
         { Parse.callee = (Parse.Ident "foo");
           args' = { Parse.inner = []; pos = 1:4 } });
      pos = 1:1 } |}]

let%expect_test _ =
  parse "foo(5, 'o', bar)" |> show_ast |> print_endline;
  [%expect
    {|
    { Parse.inner =
      (Parse.Call
         { Parse.callee = (Parse.Ident "foo");
           args' =
           { Parse.inner =
             [{ Parse.inner =
                (Parse.Decl'
                   { Parse.kind' = None;
                     name_or_count = { Parse.inner = (Parse.Num'' 5); pos = 1:5 };
                     type_'' = None; value'' = None });
                pos = 1:5 };
               { Parse.inner = (Parse.Value' (Parse.Rune 'o')); pos = 1:8 };
               { Parse.inner =
                 (Parse.Decl'
                    { Parse.kind' = None;
                      name_or_count =
                      { Parse.inner = (Parse.Ident'' "bar"); pos = 1:13 };
                      type_'' = None; value'' = None });
                 pos = 1:13 }
               ];
             pos = 1:4 }
           });
      pos = 1:1 } |}]

let%test_unit _ =
  let f () = parse "foo.=" in
  assert_raises (UnexpectedToken (Assign, { row = 1; col = 5 })) f

let%test_unit _ =
  let f () = parse "(" in
  assert_raises (UnexpectedEOF { row = 1; col = 2 }) f

let%test_unit _ =
  let f () = parse "(proc" in
  assert_raises (UnexpectedEOF { row = 1; col = 6 }) f

let%test_unit _ =
  let f () = parse "(foo" in
  assert_raises (UnexpectedEOF { row = 1; col = 5 }) f

let%test_unit _ =
  let f () = parse "(foo: Bar" in
  assert_raises (UnexpectedEOF { row = 1; col = 10 }) f

let%test_unit _ =
  let f () = parse "(foo: Bar = 5" in
  assert_raises (UnexpectedEOF { row = 1; col = 14 }) f

let%test_unit _ =
  let f () = parse "(foo: Bar = 5[" in
  assert_raises (UnexpectedToken (OpenSquareBrkt, { row = 1; col = 14 })) f
