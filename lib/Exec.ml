exception TODO

module StringMap = Map.Make (String)

type value =
  | Num of int
  | Rune of char
  | SumVariant of sum_variant
  | Prod of prod
  | Proc of (prod -> Lex.pos -> value)
[@@deriving show]

and scope_entry = Mut of value option ref | Val of value
and prod_field = { name : string; entry : scope_entry }
and prod = prod_field list
and sum_variant = { id : int; disc : int; field : value option }

let scope_entry_from_kind kind value =
  match kind with Parse.Mut -> Mut (ref (Some value)) | Val -> Val value

exception UseBeforeInitialization of string * Lex.pos

let () =
  Printexc.register_printer (function
    | UseBeforeInitialization (name, { row; col }) ->
        Some
          (Printf.sprintf "%d:%d: use of \"%s\" before initialization" row col
             name)
    | _ -> None)

let value_from_scope_entry name pos = function
  | Mut value_ref -> (
      match !value_ref with
      | Some value -> value
      | None -> raise (UseBeforeInitialization (name, pos)))
  | Val value -> value

let unit_val = Prod []

type 'a ctrl_of =
  | Brk of Lex.pos
  | Ctn of Lex.pos
  | Ret of value option * Lex.pos
  | None of 'a

let map_ctrl_of f = function
  | Brk pos -> Brk pos
  | Ctn pos -> Ctn pos
  | Ret (value, pos) -> Ret (value, pos)
  | None a -> f a

exception NumAsArgumentName of Lex.pos

let () =
  Printexc.register_printer (function
    | NumAsArgumentName { row; col } ->
        Some (Printf.sprintf "%d:%d: number specified as argument name" row col)
    | _ -> None)

exception ValueAsArgument of Lex.pos

let () =
  Printexc.register_printer (function
    | ValueAsArgument { row; col } ->
        Some
          (Printf.sprintf "%d:%d: value specified in function declaration" row
             col)
    | _ -> None)

exception MutArgument of Lex.pos

let () =
  Printexc.register_printer (function
    | MutArgument { row; col } ->
        Some (Printf.sprintf "%d:%d: argument specified as mut" row col)
    | _ -> None)

let rec args_names = function
  | [] -> []
  | {
      Parse.inner =
        Parse.Decl'
          {
            kind';
            name_or_count = { inner = Ident'' name; pos = _ };
            type_'' = _;
            value'' = _;
          };
      pos;
    }
    :: fields ->
      let () =
        match kind' with Some Parse.Mut -> raise (MutArgument pos) | _ -> ()
      in
      name :: args_names fields
  | {
      inner =
        Decl'
          {
            kind' = _;
            name_or_count = { inner = Num'' _; pos };
            type_'' = _;
            value'' = _;
          };
      pos = _;
    }
    :: _ ->
      raise (NumAsArgumentName pos)
  | { inner = Value' _; pos } :: _ -> raise (ValueAsArgument pos)

exception InvalidBinopOperands of value * value * Lex.pos
exception InvalidUnaryOperand of value * Lex.pos
exception InvalidIfCond of value * Lex.pos
exception UninitializedVal of string * Lex.pos
exception UnboundIdent of string * Lex.pos

let () =
  Printexc.register_printer (function
    | UnboundIdent (name, { row; col }) ->
        Some (Printf.sprintf "%d:%d: unbound ident: \"%s\"" row col name)
    | _ -> None)

exception Redeclaration of string * Lex.pos
exception ImmutableAssign of Parse.ident_or_field * Lex.pos
exception InvalidAccess of value * Lex.pos
exception InvalidField of string * Lex.pos
exception InvalidCallArgs of string list * prod * Lex.pos
exception InvalidCallee of value * Lex.pos
exception UnexpectedCtrl of Lex.pos

let bool_id = Oo.id (object end)

let bool_from_bool b =
  SumVariant { id = bool_id; disc = (if b then 1 else 0); field = None }

let is_bool { id; _ } = id == bool_id
let bool_not { disc; _ } = bool_from_bool (disc = 0)
let bool_eq { disc = d1; _ } { disc = d2; _ } = bool_from_bool (d1 = d2)
let bool_ne { disc = d1; _ } { disc = d2; _ } = bool_from_bool (d1 != d2)

let rec exec_expr { Parse.inner = expr; pos } scopes =
  let exec_binop = exec_binop pos scopes in
  let exec_uop = exec_uop scopes in
  let exec_num_binop = exec_num_binop pos scopes in
  let exec_bool_binop = exec_bool_binop pos scopes in
  match expr with
  | Parse.Plus binop -> exec_num_binop binop ( + )
  | Mins binop -> exec_num_binop binop ( - )
  | Astr binop -> exec_num_binop binop ( * )
  | Slsh binop -> exec_num_binop binop ( / )
  | Perc binop -> exec_num_binop binop ( mod )
  | And binop -> exec_bool_binop binop ( && )
  | Or binop -> exec_bool_binop binop ( || )
  | Not operand ->
      exec_uop operand (function
        | SumVariant variant when is_bool variant -> None (bool_not variant)
        | invalid -> raise (InvalidUnaryOperand (invalid, pos)))
  | UnaryMins operand ->
      exec_uop operand (function
        | Num n -> None (Num (-n))
        | invalid -> raise (InvalidUnaryOperand (invalid, pos)))
  | Eq binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | SumVariant v1, SumVariant v2 when is_bool v1 && is_bool v2 ->
              bool_eq v1 v2
          | Num n1, Num n2 -> bool_from_bool (n1 = n2)
          | Rune r1, Rune r2 -> bool_from_bool (r1 = r2)
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Ne binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | SumVariant v1, SumVariant v2 when is_bool v1 && is_bool v2 ->
              bool_ne v1 v2
          | Num n1, Num n2 -> bool_from_bool (n1 != n2)
          | Rune r1, Rune r2 -> bool_from_bool (r1 != r2)
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Le binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Num n1, Num n2 -> bool_from_bool (n1 <= n2)
          | Rune r1, Rune r2 -> bool_from_bool (r1 <= r2)
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Lt binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Num n1, Num n2 -> bool_from_bool (n1 < n2)
          | Rune r1, Rune r2 -> bool_from_bool (r1 < r2)
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Sum _variants -> raise TODO
  | Prod fields ->
      let ctrl_of_fields = exec_prod fields scopes in
      map_ctrl_of (fun fields -> None (Prod fields)) ctrl_of_fields
  | Ident i -> (
      match List.find_map (fun scope -> StringMap.find_opt i !scope) scopes with
      | Some entry -> None (value_from_scope_entry i pos entry)
      | None -> raise (UnboundIdent (i, pos)))
  | Block stmts -> exec_block stmts scopes
  | If { cond; if_branch; else_branch } ->
      let ctrl = exec_expr cond scopes in
      map_ctrl_of
        (function
          | SumVariant variant when is_bool variant && variant.disc = 1 ->
              exec_expr if_branch scopes
          | SumVariant variant when is_bool variant && variant.disc = 0 -> (
              match else_branch with
              | Some else_branch -> exec_expr else_branch scopes
              | None -> None unit_val)
          | cond -> raise (InvalidIfCond (cond, pos)))
        ctrl
  | ProcType { args = _; return_type = _ } -> raise TODO
  | Proc
      { type_' = { args = { inner = args; pos = _ }; return_type = _ }; body }
    ->
      let expected = args_names args in
      None
        (Proc
           (fun fields call_pos ->
             if
               List.length fields != List.length expected
               || not
                    (List.for_all2
                       (fun expected_name actual_field ->
                         expected_name = actual_field.name
                         &&
                         match
                           (List.find
                              (fun { name; _ } -> name = expected_name)
                              fields)
                             .entry
                         with
                         | Mut _ -> false
                         | Val _ -> true)
                       expected fields)
             then raise (InvalidCallArgs (expected, fields, call_pos))
             else
               let fields_scope =
                 List.fold_left
                   (fun scope { name; entry } -> StringMap.add name entry scope)
                   StringMap.empty fields
               in
               let ctrl = exec_block body (ref fields_scope :: scopes) in
               match ctrl with
               | None value -> value
               | Brk pos | Ctn pos -> raise (UnexpectedCtrl pos)
               | Ret (value, _) -> Option.value value ~default:unit_val))
  | Field { accessed; accessor = { inner = accessor; pos = accessor_pos } } ->
      let ctrl = exec_expr { inner = accessed; pos } scopes in
      map_ctrl_of
        (function
          | Prod fields -> (
              match
                List.find_opt (fun { name; _ } -> name = accessor) fields
              with
              | Some { entry; _ } ->
                  None (value_from_scope_entry accessor pos entry)
              | None -> raise (InvalidField (accessor, accessor_pos)))
          | invalid -> raise (InvalidAccess (invalid, pos)))
        ctrl
  | Call { callee; args' = { inner = args; pos = args_pos } } ->
      let ctrl = exec_expr { inner = callee; pos } scopes in
      map_ctrl_of
        (function
          | Proc f ->
              let ctrl = exec_prod args scopes in
              map_ctrl_of (fun fields -> None (f fields args_pos)) ctrl
          | invalid -> raise (InvalidCallee (invalid, pos)))
        ctrl
  | Num n -> None (Num n)
  | Rune r -> None (Rune r)
  | String _s -> raise TODO

and exec_binop pos scopes { Parse.lhs; rhs } op =
  let ctrl = exec_expr { inner = lhs; pos } scopes in
  map_ctrl_of
    (fun lhs ->
      let ctrl = exec_expr rhs scopes in
      map_ctrl_of (fun rhs -> None (op lhs rhs)) ctrl)
    ctrl

and exec_num_binop pos scopes binop op =
  exec_binop pos scopes binop (fun lhs rhs ->
      match (lhs, rhs) with
      | Num n1, Num n2 -> Num (op n1 n2)
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))

and exec_bool_binop pos scopes binop op =
  exec_binop pos scopes binop (fun lhs rhs ->
      match (lhs, rhs) with
      | SumVariant v1, SumVariant v2 when is_bool v1 && is_bool v2 ->
          let d1 = v1.disc != 0 in
          let d2 = v2.disc != 0 in
          bool_from_bool (op d1 d2)
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))

and exec_uop scopes operand op =
  let ctrl = exec_expr operand scopes in
  map_ctrl_of (fun operand -> op operand) ctrl

and exec_prod fields scopes =
  let _, ctrl =
    List.fold_left
      (fun (prev_kind, ctrl) { Parse.inner = field; pos } ->
        match ctrl with
        | None fields -> (
            match field with
            | Parse.Decl'
                {
                  kind';
                  name_or_count = { inner = Ident'' name; _ };
                  value'' = Some value;
                  _;
                } -> (
                let kind = Option.value kind' ~default:prev_kind in
                let ctrl = exec_expr value scopes in
                let () =
                  match
                    List.find_opt
                      (fun { name = existing_name; _ } -> existing_name = name)
                      fields
                  with
                  | Some { name; _ } -> raise (Redeclaration (name, pos))
                  | None -> ()
                in
                match ctrl with
                | None value ->
                    let entry = scope_entry_from_kind kind value in
                    (kind, None (fields @ [ { name; entry } ]))
                | Brk pos -> (kind, Brk pos)
                | Ctn pos -> (kind, Ctn pos)
                | Ret (value, pos) -> (kind, Ret (value, pos)))
            | _ -> raise TODO)
        | Brk pos -> (prev_kind, Brk pos)
        | Ctn pos -> (prev_kind, Ctn pos)
        | Ret (value, pos) -> (prev_kind, Ret (value, pos)))
      (Parse.Val, None []) fields
  in
  ctrl

and exec_block stmts scopes =
  match stmts with
  | [ { inner = Expr expr; pos } ] ->
      exec_expr { inner = expr; pos } (ref StringMap.empty :: scopes)
  | [ stmt ] ->
      let ctrl = exec_stmt stmt (ref StringMap.empty :: scopes) in
      map_ctrl_of (fun () -> None unit_val) ctrl
  | stmts ->
      let ctrl = exec_nonsingle_block stmts (ref StringMap.empty :: scopes) in
      map_ctrl_of (fun () -> None unit_val) ctrl

and exec_nonsingle_block stmts scopes =
  match stmts with
  | stmt :: stmts ->
      let ctrl = exec_stmt stmt scopes in
      map_ctrl_of (fun _ -> exec_nonsingle_block stmts scopes) ctrl
  | [] -> None ()

(* scopes must be non-empty. *)
and exec_stmt { Parse.inner = stmt; pos } scopes =
  match stmt with
  | Parse.Brk -> Brk pos
  | Ctn -> Ctn pos
  | Ret value -> (
      match value with
      | Some value ->
          let ctrl = exec_expr value scopes in
          map_ctrl_of (fun value -> Ret (Some value, pos)) ctrl
      | None -> Ret (None, pos))
  | Decl
      {
        kind = { inner = kind; pos = _ };
        name = { inner = name; pos = _ };
        type_ = _;
        value;
      } -> (
      match (kind, value) with
      | _, Some value ->
          let ctrl = exec_expr value scopes in
          map_ctrl_of
            (fun value ->
              let entry = scope_entry_from_kind kind value in
              let scope = List.hd scopes in
              let () =
                match StringMap.find_opt name !scope with
                | Some _ -> raise (Redeclaration (name, pos))
                | None -> ()
              in
              scope := StringMap.add name entry !scope;
              None ())
            ctrl
      | Mut, None ->
          let scope = List.hd scopes in
          let () =
            match StringMap.find_opt name !scope with
            | Some _ -> raise (Redeclaration (name, pos))
            | None -> ()
          in
          scope := StringMap.add name (Mut (ref Option.None)) !scope;
          None ()
      | Val, None -> raise (UninitializedVal (name, pos)))
  | Assign { assignee; value' } -> (
      let try_scope_entry_assign assignee' scopes =
        match assignee' with
        | Mut value_ref ->
            let ctrl = exec_expr value' scopes in
            map_ctrl_of
              (fun value ->
                value_ref := Some value;
                None ())
              ctrl
        | _ -> raise (ImmutableAssign (assignee, pos))
      in
      match assignee with
      | Ident' i -> (
          match
            List.find_map (fun scope -> StringMap.find_opt i !scope) scopes
          with
          | Some assignee -> try_scope_entry_assign assignee scopes
          | None -> raise (UnboundIdent (i, pos)))
      | Field' { accessed; accessor = { inner = accessor; pos = accessor_pos } }
        ->
          let ctrl = exec_expr { inner = accessed; pos } scopes in
          map_ctrl_of
            (function
              | Prod fields -> (
                  match
                    List.find_opt (fun { name; _ } -> name = accessor) fields
                  with
                  | Some { entry; _ } -> try_scope_entry_assign entry scopes
                  | None -> raise (InvalidField (accessor, accessor_pos)))
              | invalid -> raise (InvalidAccess (invalid, pos)))
            ctrl)
  | Loop body -> exec_loop body scopes
  | Expr expr ->
      let value = exec_expr { inner = expr; pos } scopes in
      map_ctrl_of (fun _ -> None ()) value

and exec_loop body scopes =
  let ctrl = exec_expr body scopes in
  match ctrl with
  | Brk _ -> None ()
  | Ret (value, pos) -> Ret (value, pos)
  | _ -> exec_loop body scopes

let intrinsics =
  [
    {
      name = "bsPrintln";
      entry =
        Val
          (Proc
             (fun fields pos ->
               match fields with
               | [ { name = "value"; entry } ] ->
                   let value = value_from_scope_entry "value" pos entry in
                   let () = show_value value |> print_endline in
                   unit_val
               | _ -> raise (InvalidCallArgs ([ "value" ], fields, pos))));
    };
  ]

let builtins =
  let builtins = StringMap.empty in
  let builtins = StringMap.add "False" (Val (bool_from_bool false)) builtins in
  let builtins = StringMap.add "True" (Val (bool_from_bool true)) builtins in
  StringMap.add "intrinsics" (Val (Prod intrinsics)) builtins

let exec_ast ast =
  let ctrl = exec_expr ast [ ref builtins ] in
  match ctrl with
  | None value -> value
  | Brk pos | Ctn pos | Ret (_, pos) -> raise (UnexpectedCtrl pos)

exception ExpectedProc

let exec path =
  let text = Core.In_channel.read_lines path in
  let ast = String.concat "\n" text |> Parse.parse in
  let _ =
    match exec_ast ast with
    | Proc f -> f [] { row = 0; col = 0 }
    | _ -> raise ExpectedProc
  in
  ()

let assert_raises = OUnit2.assert_raises
let parse = Parse.parse

let%test _ =
  let ast = parse "5 + 9" in
  Num 14 = exec_ast ast

let%test_unit _ =
  let ast = parse "False + True" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       (bool_from_bool false, bool_from_bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 - 9" in
  Num (-4) = exec_ast ast

let%test_unit _ =
  let ast = parse "False - True" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       (bool_from_bool false, bool_from_bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 * 9" in
  Num 45 = exec_ast ast

let%test_unit _ =
  let ast = parse "False * True" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       (bool_from_bool false, bool_from_bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 / 9" in
  Num 0 = exec_ast ast

let%test_unit _ =
  let ast = parse "False / True" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       (bool_from_bool false, bool_from_bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 % 9" in
  Num 5 = exec_ast ast

let%test_unit _ =
  let ast = parse "False % True" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       (bool_from_bool false, bool_from_bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "True && False" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "True && True" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "5 && 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidBinopOperands (Num 5, Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "False || True" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "True || False" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "False || False" in
  bool_from_bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "5 || 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidBinopOperands (Num 5, Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "!False" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "!True" in
  bool_from_bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "!5" in
  let f () = exec_ast ast in
  assert_raises (InvalidUnaryOperand (Num 5, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "-5" in
  Num (-5) = exec_ast ast

let%test_unit _ =
  let ast = parse "-False" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidUnaryOperand (bool_from_bool false, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "False == True" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "True == True" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "5 == 9" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "5 == 5" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' == 'q'" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' == 'r'" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "False != True" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "True != True" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "5 != 9" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "5 != 5" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' != 'q'" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' != 'r'" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "5 <= 5" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "9 <= 5" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' <= 'q'" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'q' <= 'q'" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "False <= True" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       (bool_from_bool false, bool_from_bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 < 5" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "5 < 9" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' < 'r'" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'q' <= 'r'" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "False < True" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       (bool_from_bool false, bool_from_bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "if True 5 else 9" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "if False 5 else 9" in
  Num 9 = exec_ast ast

let%test _ =
  let ast = parse "if False 5" in
  unit_val = exec_ast ast

let%test_unit _ =
  let ast = parse "if 9 5 else 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidIfCond (Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "()" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9)" in
  Prod [ { name = "i"; entry = Val (Num 9) } ] = exec_ast ast

let%test_unit _ =
  let ast = parse "(val i = 9, val i = 9)" in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { row = 1; col = 13 })) f

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = True)" in
  Prod
    [
      { name = "i"; entry = Val (Num 9) };
      { name = "j"; entry = Val (Rune 'a') };
      { name = "k"; entry = Mut (ref (Some (bool_from_bool true))) };
    ]
  = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9).i" in
  Num 9 = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = True).j" in
  Rune 'a' = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = True).k" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = True).k" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "().i" in
  let f () = exec_ast ast in
  assert_raises (InvalidField ("i", { row = 1; col = 4 })) f

let%test_unit _ =
  let ast = parse "1.i" in
  let f () = exec_ast ast in
  assert_raises (InvalidAccess (Num 1, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "{ proc() { } }()" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "{ proc(val i: Nat) { i + 1 } }(val i = 2)" in
  Num 3 = exec_ast ast

let%test _ =
  let ast =
    parse "{ proc(val i: Nat, val j: Nat) { i * j } }(val i = 2, val j = 9)"
  in
  Num 18 = exec_ast ast

let%test _ =
  let ast = parse "{ proc(val i, j: Nat) { i * j } }(val i = 2, val j = 9)" in
  Num 18 = exec_ast ast

let%test_unit _ =
  let ast = parse "{ proc(val i: Nat) { i } }(val j = 2)" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidCallArgs
       ([ "i" ], [ { name = "j"; entry = Val (Num 2) } ], { row = 1; col = 27 }))
    f

let%test_unit _ =
  let ast = parse "{ proc(val i: Nat) { i } }()" in
  let f () = exec_ast ast in
  assert_raises (InvalidCallArgs ([ "i" ], [], { row = 1; col = 27 })) f

let%test_unit _ =
  let ast = parse "proc(mut i: Nat) { i }" in
  let f () = exec_ast ast in
  assert_raises (MutArgument { row = 1; col = 6 }) f

let%test_unit _ =
  let ast = parse "proc(val 5: Nat) { }" in
  let f () = exec_ast ast in
  assert_raises (NumAsArgumentName { row = 1; col = 10 }) f

let%test_unit _ =
  let ast = parse "proc('a') { }" in
  let f () = exec_ast ast in
  assert_raises (ValueAsArgument { row = 1; col = 6 }) f

let%test_unit _ =
  let ast = parse "{ proc() { foo } }()" in
  let f () = exec_ast ast in
  assert_raises (UnboundIdent ("foo", { row = 1; col = 12 })) f

let%test _ =
  let ast =
    parse
      {|
    {
      proc() {
        mut i = 0
        loop {
          i = 2
          brk
        }
        ret i
      }
    }()
  |}
  in
  Num 2 = exec_ast ast

let%test_unit _ =
  let ast =
    parse
      {|
    {
      proc() {
        mut i
        ret i
      }
    }()
  |}
  in
  let f () = exec_ast ast in
  assert_raises (UseBeforeInitialization ("i", { row = 5; col = 13 })) f

let%test _ =
  let ast =
    parse
      {|
    {
      proc() {
        mut b = False
        loop {
          if b {
            brk
          }

          b = True

          ctn

          ret False
        }

        ret True
      }
    }()
  |}
  in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { loop { ret 'a' } } }()" in
  Rune 'a' = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    {
      proc() {
        if { if True { ret 9 } else True } {
          ret 3
        }

        ret 5
      }
    }()
  |}
  in
  Num 9 = exec_ast ast

let%test_unit _ =
  let ast = parse "{ proc() { brk } }()" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { row = 1; col = 12 }) f

let%test_unit _ =
  let ast = parse "{ proc() { ctn } }()" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { row = 1; col = 12 }) f

let%test _ =
  let ast = parse "{ proc() { { ret 5 }.foo } }()" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { { ret 5 }() } }()" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { { ret 5 } + 1 } }()" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { 1 + { ret 5 } } }()" in
  Num 5 = exec_ast ast

let%test_unit _ =
  let ast = parse "1()" in
  let f () = exec_ast ast in
  assert_raises (InvalidCallee (Num 1, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "{ proc() { mut i } }()" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { ret } }()" in
  unit_val = exec_ast ast

let%test_unit _ =
  let ast =
    parse
      {|
    {
      proc() {
        val i = 1
        val i = 1
      }
    }()
  |}
  in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { row = 5; col = 9 })) f

let%test_unit _ =
  let ast =
    parse
      {|
    {
      proc() {
        mut i
        mut i
      }
    }()
  |}
  in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { row = 5; col = 9 })) f

let%test_unit _ =
  let ast = parse "{ proc() { val i } }()" in
  let f () = exec_ast ast in
  assert_raises (UninitializedVal ("i", { row = 1; col = 12 })) f

let%test_unit _ =
  let ast =
    parse
      {|
    {
      proc() {
        val i = 1
        i = 2
      }
    }()
  |}
  in
  let f () = exec_ast ast in
  assert_raises (ImmutableAssign (Ident' "i", { row = 5; col = 9 })) f

let%test_unit _ =
  let ast = parse {|
    {
      proc() {
        i = 1
      }
    }()
  |} in
  let f () = exec_ast ast in
  assert_raises (UnboundIdent ("i", { row = 4; col = 9 })) f

let%test_unit _ =
  let ast = parse "{ brk }" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { row = 1; col = 3 }) f

let%test_unit _ =
  let ast = parse "{ ctn }" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { row = 1; col = 3 }) f

let%test_unit _ =
  let ast = parse "{ ret }" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { row = 1; col = 3 }) f

let%test _ =
  let ast =
    parse
      {|
    {
      proc() {
        mut p = (mut f = 5)
        p.f = 9
        ret p.f
      }
    }()
  |}
  in
  Num 9 = exec_ast ast

let%test_unit _ =
  let ast =
    parse
      {|
    {
      proc() {
        mut p = (mut f = 5)
        p.bogus = 9
        ret p.f
      }
    }()
  |}
  in
  let f () = exec_ast ast in
  assert_raises (InvalidField ("bogus", { row = 5; col = 11 })) f

let%test_unit _ =
  let ast =
    parse
      {|
    {
      proc() {
        val i = 1
        i.bogus = 9
        ret i.f
      }
    }()
  |}
  in
  let f () = exec_ast ast in
  assert_raises (InvalidAccess (Num 1, { row = 5; col = 9 })) f
