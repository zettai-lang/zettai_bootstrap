exception TODO

module StringMap = Map.Make (String)

(*
  TODO: strings aren't really primitive values... but we do need to be able to
  represent literals somehow... might have to figure out how this works with
  intrinsics and such.
*)
type value =
  | Bool of bool
  | Num of int
  | Rune of char
  | String of string
  | Prod of prod

and scope_entry = Pre of value | Val of value | Var of value option ref
and prod = scope_entry StringMap.t

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

let unit_val = Prod StringMap.empty

type 'a ctrl_of = Brk | Ctn | Ret of value option | None of 'a

let map_ctrl_of f = function
  | Brk -> Brk
  | Ctn -> Ctn
  | Ret value -> Ret value
  | None a -> f a

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
      exec_uop operand (fun operand ->
          match operand with
          | Bool b -> None (Bool (not b))
          | _ -> raise (InvalidUnaryOperand (operand, pos)))
  | UnaryMins operand ->
      exec_uop operand (fun operand ->
          match operand with
          | Num n -> None (Num (-n))
          | _ -> raise (InvalidUnaryOperand (operand, pos)))
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
      let ctrl_of_fields, scopes = exec_prod (List.rev fields) scopes in
      (map_ctrl_of (fun fields -> None (Prod fields)) ctrl_of_fields, scopes)
  | Ident i -> (
      match List.find_map (fun scope -> StringMap.find_opt i scope) scopes with
      | Some entry -> (None (value_from_scope_entry i pos entry), scopes)
      | None -> raise (UnboundIdent (i, pos)))
  | Block stmts -> exec_block stmts scopes
  | If { cond; if_branch; else_branch } -> (
      let ctrl, scopes = exec_expr cond scopes in
      match ctrl with
      | None (Bool true) -> exec_expr if_branch scopes
      | None (Bool false) -> (
          match else_branch with
          | Some else_branch -> exec_expr else_branch scopes
          | None -> (None unit_val, scopes))
      | None cond -> raise (InvalidIfCond (cond, pos))
      | ctrl -> (ctrl, scopes))
  | ProcType { args = _; return_type = _ } -> raise TODO
  | Proc { type_' = { args = _; return_type = _ }; body = _ } -> raise TODO
  | Field { accessed; accessor = { inner = accessor; pos = accessor_pos } } -> (
      let ctrl, scopes = exec_expr { inner = accessed; pos } scopes in
      match ctrl with
      | None (Prod fields) -> (
          match StringMap.find_opt accessor fields with
          | Some entry ->
              (None (value_from_scope_entry accessor pos entry), scopes)
          | None -> raise (InvalidField (accessor, accessor_pos)))
      | None invalid -> raise (InvalidAccess (invalid, pos))
      | ctrl -> (ctrl, scopes))
  | Call { callee = _; args' = _ } -> raise TODO
  | Bool b -> (None (Bool b), scopes)
  | Num n -> (None (Num n), scopes)
  | Rune r -> (None (Rune r), scopes)
  | String s -> (None (String s), scopes)

and exec_binop pos scopes { Parse.lhs; rhs } op =
  let ctrl, scopes = exec_expr { inner = lhs; pos } scopes in
  match ctrl with
  | None lhs -> (
      let ctrl, scopes = exec_expr rhs scopes in
      match ctrl with
      | None rhs -> (None (op lhs rhs), scopes)
      | ctrl -> (ctrl, scopes))
  | ctrl -> (ctrl, scopes)

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
  let ctrl, scopes = exec_expr operand scopes in
  match ctrl with None operand -> (op operand, scopes) | ctrl -> (ctrl, scopes)

and exec_prod fields scopes =
  match fields with
  | [] -> (None StringMap.empty, scopes)
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
    :: fields -> (
      let ctrl, scopes = exec_prod fields scopes in
      match ctrl with
      | None fields -> (
          let () =
            match StringMap.find_opt name fields with
            | Some _ -> raise (Redeclaration (name, pos))
            | None -> ()
          in
          let ctrl, scopes = exec_expr value scopes in
          match ctrl with
          | None value ->
              let entry = scope_entry_from_kind kind value in
              let fields = StringMap.add name entry fields in
              (None fields, scopes)
          | Brk -> (Brk, scopes)
          | Ctn -> (Ctn, scopes)
          | Ret value -> (Ret value, scopes))
      | ctrl -> (ctrl, scopes))
  | _ -> raise TODO

and exec_block stmts scopes =
  match stmts with
  | [ { inner = Expr expr; pos } ] -> exec_expr { inner = expr; pos } scopes
  | [ stmt ] ->
      let ctrl, scopes = exec_stmt stmt (StringMap.empty :: scopes) in
      (map_ctrl_of (fun () -> None unit_val) ctrl, List.tl scopes)
  | stmts ->
      let ctrl, scopes =
        exec_nonsingle_block stmts (StringMap.empty :: scopes)
      in
      (map_ctrl_of (fun () -> None unit_val) ctrl, scopes)

and exec_nonsingle_block stmts scopes =
  match stmts with
  | stmt :: stmts -> (
      let ctrl, scopes = exec_stmt stmt scopes in
      match ctrl with
      | None _ -> exec_nonsingle_block stmts scopes
      | ctrl -> (ctrl, scopes))
  | [] -> (None (), scopes)

(* scopes must be non-empty. *)
and exec_stmt { Parse.inner = stmt; pos } scopes =
  match stmt with
  | Parse.Brk -> (Brk, scopes)
  | Ctn -> (Ctn, scopes)
  | Ret value -> (
      match value with
      | Some value ->
          let ctrl, scopes = exec_expr value scopes in
          (map_ctrl_of (fun value -> Ret (Some value)) ctrl, scopes)
      | None -> (Ret None, scopes))
  (* TODO: typecheck? *)
  | Decl
      {
        kind = { inner = kind; pos = _ };
        name = { inner = name; pos = _ };
        type_ = _;
        value;
      } -> (
      let scope, scopes =
        match scopes with
        | scope :: scopes -> (scope, scopes)
        (* Because scopes must be non-empty. *)
        | [] -> raise Unreachable
      in
      let () =
        match StringMap.find_opt name scope with
        | Some _ -> raise (Redeclaration (name, pos))
        | None -> ()
      in
      match (kind, value) with
      | _, Some value -> (
          let ctrl, scopes = exec_expr value scopes in
          match ctrl with
          | None value ->
              let entry = scope_entry_from_kind kind value in
              let scope = StringMap.add name entry scope in
              (None (), scope :: scopes)
          | ctrl -> (map_ctrl_of (fun _ -> None ()) ctrl, scopes))
      | Pre, None -> raise (UninitializedPre (name, pos))
      | Val, None -> raise (UninitializedVal (name, pos))
      | Var, None ->
          let scope = StringMap.add name (Var (ref Option.None)) scope in
          (None (), scope :: scopes))
  | Assign { assignee; value' } -> (
      let try_scope_entry_assign assignee' =
        match assignee' with
        | Var value_ref ->
            let ctrl, scopes = exec_expr value' scopes in
            ( map_ctrl_of
                (fun value ->
                  value_ref := Some value;
                  None ())
                ctrl,
              scopes )
        | _ -> raise (ImmutableAssign (assignee, pos))
      in
      match assignee with
      | Ident' i -> (
          match
            List.find_map (fun scope -> StringMap.find_opt i scope) scopes
          with
          | Some assignee -> try_scope_entry_assign assignee
          | None -> raise (UnboundIdent (i, pos)))
      | Field' { accessed; accessor = { inner = accessor; pos = accessor_pos } }
        -> (
          let ctrl, scopes = exec_expr { inner = accessed; pos } scopes in
          match ctrl with
          | None (Prod fields) -> (
              match StringMap.find_opt accessor fields with
              | Some field -> try_scope_entry_assign field
              | None -> raise (InvalidField (accessor, accessor_pos)))
          | None invalid -> raise (InvalidAccess (invalid, pos))
          | ctrl -> (map_ctrl_of (fun _ -> raise Unreachable) ctrl, scopes)))
  | Loop body -> exec_loop body scopes
  | Expr expr ->
      let value, scopes = exec_expr { inner = expr; pos } scopes in
      (map_ctrl_of (fun _ -> None ()) value, List.tl scopes)

and exec_loop body scopes =
  let ctrl, scopes = exec_expr body scopes in
  match ctrl with
  | Brk -> (None (), scopes)
  | Ret _ -> (map_ctrl_of (fun _ -> None ()) ctrl, scopes)
  | _ -> exec_loop body scopes

let exec path _args =
  let text = Core.In_channel.read_lines path in
  let ast = String.concat "\n" text |> Parse.parse in
  let _ = exec_expr ast [] in
  ()

let assert_raises = OUnit2.assert_raises
let parse = Parse.parse

exception UnexpectedCtrl

let easy_exec_expr ast =
  let ctrl, _ = exec_expr ast [] in
  match ctrl with None value -> value | _ -> raise UnexpectedCtrl

let%test _ =
  let ast = parse "5 + 9" in
  Num 14 = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false + true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 - 9" in
  Num (-4) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false - true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 * 9" in
  Num 45 = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false * true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 / 9" in
  Num 0 = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false / true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 % 9" in
  Num 5 = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false % true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "true && false" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "true && true" in
  Bool true = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "5 && 9" in
  let f () = easy_exec_expr ast in
  assert_raises (InvalidBinopOperands (Num 5, Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "false || true" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "true || false" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "false || false" in
  Bool false = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "5 || 9" in
  let f () = easy_exec_expr ast in
  assert_raises (InvalidBinopOperands (Num 5, Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "!false" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "!true" in
  Bool false = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "!5" in
  let f () = easy_exec_expr ast in
  assert_raises (InvalidUnaryOperand (Num 5, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "-5" in
  Num (-5) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "-false" in
  let f () = easy_exec_expr ast in
  assert_raises (InvalidUnaryOperand (Bool false, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "false == true" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "true == true" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "5 == 9" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "5 == 5" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' == 'q'" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' == 'r'" in
  Bool true = easy_exec_expr ast

let%test_unit _ =
  let ast = parse {| "foo" == "bar" |} in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (String "foo", String "bar", { row = 1; col = 2 }))
    f

let%test _ =
  let ast = parse "false != true" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "true != true" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "5 != 9" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "5 != 5" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' != 'q'" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' != 'r'" in
  Bool false = easy_exec_expr ast

let%test_unit _ =
  let ast = parse {| "foo" != "bar" |} in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (String "foo", String "bar", { row = 1; col = 2 }))
    f

let%test _ =
  let ast = parse "5 <= 5" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "9 <= 5" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' <= 'q'" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "'q' <= 'q'" in
  Bool true = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false <= true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 < 5" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "5 < 9" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' < 'r'" in
  Bool false = easy_exec_expr ast

let%test _ =
  let ast = parse "'q' <= 'r'" in
  Bool true = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false < true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Bool false, Bool true, { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "if true 5 else 9" in
  Num 5 = easy_exec_expr ast

let%test _ =
  let ast = parse "if false 5 else 9" in
  Num 9 = easy_exec_expr ast

let%test _ =
  let ast = parse "if false 5" in
  unit_val = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "if 9 5 else 9" in
  let f () = easy_exec_expr ast in
  assert_raises (InvalidIfCond (Num 9, { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "()" in
  Prod StringMap.empty = easy_exec_expr ast

let%test _ =
  let ast = parse "(pre n = 5)" in
  let fields = StringMap.empty in
  let fields = StringMap.add "n" (Pre (Num 5)) fields in
  Prod fields = easy_exec_expr ast

let%test _ =
  let ast = parse "(val i = 9)" in
  let fields = StringMap.empty in
  let fields = StringMap.add "i" (Val (Num 9)) fields in
  Prod fields = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "(val i = 9, val i = 9)" in
  let f () = easy_exec_expr ast in
  assert_raises (Redeclaration ("i", { row = 1; col = 13 })) f

let%test _ =
  let ast = parse "(pre i = 9, val j = 'a', var k = true)" in
  let fields = StringMap.empty in
  let fields = StringMap.add "i" (Pre (Num 9)) fields in
  let fields = StringMap.add "j" (Val (Rune 'a')) fields in
  let fields = StringMap.add "k" (Var (ref (Some (Bool true)))) fields in
  Prod fields = easy_exec_expr ast

let%test _ =
  let ast = parse "(pre i = 9).i" in
  Num 9 = easy_exec_expr ast

let%test _ =
  let ast = parse "(pre i = 9, val j = 'a', var k = true).j" in
  Rune 'a' = easy_exec_expr ast

let%test _ =
  let ast = parse "(pre i = 9, val j = 'a', var k = true).k" in
  Bool true = easy_exec_expr ast

let%test _ =
  let ast = parse "(pre i = 9, val j = 'a', var k = true).k" in
  Bool true = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "().i" in
  let f () = easy_exec_expr ast in
  assert_raises (InvalidField ("i", { row = 1; col = 4 })) f
