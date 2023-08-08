exception TODO

module StringMap = Map.Make (String)

type value =
  | Bool of bool
  | Num of int
  | Rune of char
  | Prod of prod
  | Proc of (prod -> Lex.pos -> value)

and scope_entry = Pre of value | Val of value | Var of value option ref
and prod = { fields : scope_entry StringMap.t; order : string list }

let scope_entry_from_kind kind value =
  match kind with
  | Parse.Pre -> Pre value
  | Val -> Val value
  | Var -> Var (ref (Some value))

exception UseBeforeInitialization of string * Lex.pos

let value_from_scope_entry name pos = function
  | Pre value | Val value -> value
  | Var value_ref -> (
      match !value_ref with
      | Some value -> value
      | None -> raise (UseBeforeInitialization (name, pos)))

let unit_val = Prod { fields = StringMap.empty; order = [] }

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
exception ValueAsArgument of Lex.pos
exception VarArgument of Lex.pos

let rec args_pre_and_name ?(prev_is_pre = false) = function
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
      let kind =
        Option.map
          (fun kind ->
            match kind with
            | Parse.Pre -> true
            | Val -> false
            | Var -> raise (VarArgument pos))
          kind'
      in
      let pre = Option.value kind ~default:prev_is_pre in
      (pre, name) :: args_pre_and_name fields ~prev_is_pre:pre
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

exception Unreachable
exception InvalidBinopOperands of value * value * Lex.pos
exception InvalidUnaryOperand of value * Lex.pos
exception InvalidIfCond of value * Lex.pos
exception UninitializedPre of string * Lex.pos
exception UninitializedVal of string * Lex.pos
exception UnboundIdent of string * Lex.pos
exception Redeclaration of string * Lex.pos
exception ImmutableAssign of Parse.ident_or_field * Lex.pos
exception InvalidAccess of value * Lex.pos
exception InvalidField of string * Lex.pos
exception InvalidCallArgs of (bool * string) list * prod * Lex.pos
exception InvalidCallee of value * Lex.pos
exception UnexpectedCtrl of Lex.pos

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
        | Bool b -> None (Bool (not b))
        | invalid -> raise (InvalidUnaryOperand (invalid, pos)))
  | UnaryMins operand ->
      exec_uop operand (function
        | Num n -> None (Num (-n))
        | invalid -> raise (InvalidUnaryOperand (invalid, pos)))
  | Eq binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Bool b1, Bool b2 -> Bool (b1 = b2)
          | Num n1, Num n2 -> Bool (n1 = n2)
          | Rune r1, Rune r2 -> Bool (r1 = r2)
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Ne binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Bool b1, Bool b2 -> Bool (b1 != b2)
          | Num n1, Num n2 -> Bool (n1 != n2)
          | Rune r1, Rune r2 -> Bool (r1 != r2)
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Le binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Num n1, Num n2 -> Bool (n1 <= n2)
          | Rune r1, Rune r2 -> Bool (r1 <= r2)
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Lt binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Num n1, Num n2 -> Bool (n1 < n2)
          | Rune r1, Rune r2 -> Bool (r1 < r2)
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Sum _variants -> raise TODO
  | Prod fields ->
      let ctrl_of_fields = exec_prod (List.rev fields) scopes in
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
          | Bool true -> exec_expr if_branch scopes
          | Bool false -> (
              match else_branch with
              | Some else_branch -> exec_expr else_branch scopes
              | None -> None unit_val)
          | cond -> raise (InvalidIfCond (cond, pos)))
        ctrl
  | ProcType { args = _; return_type = _ } -> raise TODO
  (* TODO: typecheck? *)
  | Proc
      { type_' = { args = { inner = args; pos = _ }; return_type = _ }; body }
    ->
      let expected = args_pre_and_name args in
      None
        (Proc
           (fun { fields; order } call_pos ->
             if StringMap.cardinal fields != List.length order then
               raise Unreachable
             else if
               StringMap.cardinal fields != List.length expected
               || not
                    (List.for_all2
                       (fun (expected_pre, expected_name) actual_name ->
                         expected_name = actual_name
                         &&
                         match StringMap.find expected_name fields with
                         | Pre _ -> expected_pre
                         | Val _ -> not expected_pre
                         | Var _ -> false)
                       expected order)
             then
               raise (InvalidCallArgs (expected, { fields; order }, call_pos))
             else
               let ctrl = exec_block body (ref fields :: scopes) in
               match ctrl with
               | None value -> value
               | Brk pos | Ctn pos -> raise (UnexpectedCtrl pos)
               | Ret (value, _) -> Option.value value ~default:unit_val))
  | Field { accessed; accessor = { inner = accessor; pos = accessor_pos } } ->
      let ctrl = exec_expr { inner = accessed; pos } scopes in
      map_ctrl_of
        (function
          | Prod { fields; order = _ } -> (
              match StringMap.find_opt accessor fields with
              | Some entry -> None (value_from_scope_entry accessor pos entry)
              | None -> raise (InvalidField (accessor, accessor_pos)))
          | invalid -> raise (InvalidAccess (invalid, pos)))
        ctrl
  | Call { callee; args' = { inner = args; pos = args_pos } } ->
      let ctrl = exec_expr { inner = callee; pos } scopes in
      map_ctrl_of
        (function
          | Proc f ->
              let ctrl = exec_prod (List.rev args) scopes in
              map_ctrl_of (fun fields -> None (f fields args_pos)) ctrl
          | invalid -> raise (InvalidCallee (invalid, pos)))
        ctrl
  | Bool b -> None (Bool b)
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
      | Bool b1, Bool b2 -> Bool (op b1 b2)
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))

and exec_uop scopes operand op =
  let ctrl = exec_expr operand scopes in
  map_ctrl_of (fun operand -> op operand) ctrl

and exec_prod fields scopes =
  match fields with
  | [] -> None { fields = StringMap.empty; order = [] }
  (* TODO: typecheck? *)
  | {
      inner =
        Decl'
          {
            kind' = Some kind;
            name_or_count = { inner = Ident'' name; pos = _ };
            type_'' = _;
            value'' = Some value;
          };
      pos;
    }
    :: fields ->
      let ctrl = exec_prod fields scopes in
      map_ctrl_of
        (fun { fields; order } ->
          let () =
            match StringMap.find_opt name fields with
            | Some _ -> raise (Redeclaration (name, pos))
            | None -> ()
          in
          let ctrl = exec_expr value scopes in
          map_ctrl_of
            (fun value ->
              let entry = scope_entry_from_kind kind value in
              let fields = StringMap.add name entry fields in
              let order = order @ [ name ] in
              None { fields; order })
            ctrl)
        ctrl
  | _ -> raise TODO

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
  (* TODO: typecheck? *)
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
      | Pre, None -> raise (UninitializedPre (name, pos))
      | Val, None -> raise (UninitializedVal (name, pos))
      | Var, None ->
          let scope = List.hd scopes in
          let () =
            match StringMap.find_opt name !scope with
            | Some _ -> raise (Redeclaration (name, pos))
            | None -> ()
          in
          scope := StringMap.add name (Var (ref Option.None)) !scope;
          None ())
  | Assign { assignee; value' } -> (
      let try_scope_entry_assign assignee' scopes =
        match assignee' with
        | Var value_ref ->
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
              | Prod { fields; order = _ } -> (
                  match StringMap.find_opt accessor fields with
                  | Some field -> try_scope_entry_assign field scopes
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

let exec_ast ast =
  let ctrl = exec_expr ast [] in
  match ctrl with
  | None value -> value
  | Brk pos | Ctn pos | Ret (_, pos) -> raise (UnexpectedCtrl pos)

let exec path _args =
  let text = Core.In_channel.read_lines path in
  let ast = String.concat "\n" text |> Parse.parse in
  let _ = exec_ast ast in
  ()

let assert_raises = OUnit2.assert_raises
let parse = Parse.parse

let%test _ =
  let ast = parse "5 + 9" in
  Num 14 = exec_ast ast

let%test_unit _ =
  let ast = parse "false + true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 - 9" in
  Num (-4) = exec_ast ast

let%test_unit _ =
  let ast = parse "false - true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 * 9" in
  Num 45 = exec_ast ast

let%test_unit _ =
  let ast = parse "false * true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 / 9" in
  Num 0 = exec_ast ast

let%test_unit _ =
  let ast = parse "false / true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 % 9" in
  Num 5 = exec_ast ast

let%test_unit _ =
  let ast = parse "false % true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "true && false" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "true && true" in
  Bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "5 && 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidBinopOperands (Num 5, Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "false || true" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "true || false" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "false || false" in
  Bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "5 || 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidBinopOperands (Num 5, Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "!false" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "!true" in
  Bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "!5" in
  let f () = exec_ast ast in
  assert_raises (InvalidUnaryOperand (Num 5, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "-5" in
  Num (-5) = exec_ast ast

let%test_unit _ =
  let ast = parse "-false" in
  let f () = exec_ast ast in
  assert_raises (InvalidUnaryOperand (Bool false, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "false == true" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "true == true" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "5 == 9" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "5 == 5" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' == 'q'" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' == 'r'" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "false != true" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "true != true" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "5 != 9" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "5 != 5" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' != 'q'" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' != 'r'" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "5 <= 5" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "9 <= 5" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' <= 'q'" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "'q' <= 'q'" in
  Bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "false <= true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 < 5" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "5 < 9" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' < 'r'" in
  Bool false = exec_ast ast

let%test _ =
  let ast = parse "'q' <= 'r'" in
  Bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "false < true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "if true 5 else 9" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "if false 5 else 9" in
  Num 9 = exec_ast ast

let%test _ =
  let ast = parse "if false 5" in
  unit_val = exec_ast ast

let%test_unit _ =
  let ast = parse "if 9 5 else 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidIfCond (Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "()" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "(pre n = 5)" in
  let fields = StringMap.empty in
  let fields = StringMap.add "n" (Pre (Num 5)) fields in
  Prod { fields; order = [ "n" ] } = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9)" in
  let fields = StringMap.empty in
  let fields = StringMap.add "i" (Val (Num 9)) fields in
  Prod { fields; order = [ "i" ] } = exec_ast ast

let%test_unit _ =
  let ast = parse "(val i = 9, val i = 9)" in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { row = 1; col = 13 })) f

let%test _ =
  let ast = parse "(pre i = 9, val j = 'a', var k = true)" in
  let fields = StringMap.empty in
  let fields = StringMap.add "i" (Pre (Num 9)) fields in
  let fields = StringMap.add "j" (Val (Rune 'a')) fields in
  let fields = StringMap.add "k" (Var (ref (Some (Bool true)))) fields in
  Prod { fields; order = [ "i"; "j"; "k" ] } = exec_ast ast

let%test _ =
  let ast = parse "(pre i = 9).i" in
  Num 9 = exec_ast ast

let%test _ =
  let ast = parse "(pre i = 9, val j = 'a', var k = true).j" in
  Rune 'a' = exec_ast ast

let%test _ =
  let ast = parse "(pre i = 9, val j = 'a', var k = true).k" in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "(pre i = 9, val j = 'a', var k = true).k" in
  Bool true = exec_ast ast

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
    parse "{ proc(pre i: Nat, val j: Nat) { i * j } }(pre i = 2, val j = 9)"
  in
  Num 18 = exec_ast ast

let%test _ =
  let ast = parse "{ proc(pre i, j: Nat) { i * j } }(pre i = 2, pre j = 9)" in
  Num 18 = exec_ast ast

let%test_unit _ =
  let ast = parse "{ proc(pre i: Nat) { i } }(val i = 2)" in
  let f () = exec_ast ast in
  let fields = StringMap.empty in
  let fields = StringMap.add "i" (Val (Num 2)) fields in
  assert_raises
    (InvalidCallArgs
       ([ (true, "i") ], { fields; order = [ "i" ] }, { row = 1; col = 27 }))
    f

let%test_unit _ =
  let ast = parse "{ proc(pre i: Nat) { i } }(var i = 2)" in
  let f () = exec_ast ast in
  let fields = StringMap.empty in
  let fields = StringMap.add "i" (Var (ref (Some (Num 2)))) fields in
  assert_raises
    (InvalidCallArgs
       ([ (true, "i") ], { fields; order = [ "i" ] }, { row = 1; col = 27 }))
    f

let%test_unit _ =
  let ast = parse "{ proc(val i: Nat) { i } }()" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidCallArgs
       ( [ (false, "i") ],
         { fields = StringMap.empty; order = [] },
         { row = 1; col = 27 } ))
    f

let%test_unit _ =
  let ast = parse "proc(var i: Nat) { i }" in
  let f () = exec_ast ast in
  assert_raises (VarArgument { row = 1; col = 6 }) f

let%test_unit _ =
  let ast = parse "proc(val 5: Nat) { }" in
  let f () = exec_ast ast in
  assert_raises (NumAsArgumentName { row = 1; col = 10 }) f

let%test_unit _ =
  let ast = parse "proc(true) { }" in
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
        var i = 0
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
        var i
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
        var b = false
        loop {
          if b {
            brk
          }

          b = true

          ctn

          ret false
        }

        ret true
      }
    }()
  |}
  in
  Bool true = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { loop { ret 'a' } } }()" in
  Rune 'a' = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    {
      proc() {
        if { if true { ret 9 } else true } {
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
  let ast = parse "{ proc() { var i } }()" in
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
        var i
        var i
      }
    }()
  |}
  in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { row = 5; col = 9 })) f

let%test_unit _ =
  let ast = parse "{ proc() { pre i } }()" in
  let f () = exec_ast ast in
  assert_raises (UninitializedPre ("i", { row = 1; col = 12 })) f

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
        var p = (var f = 5)
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
        var p = (var f = 5)
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
