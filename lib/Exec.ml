exception TODO

(*
  TODO: strings aren't really primitive values... but we do need to be able to
  represent literals somehow... might have to figure out how this works with
  intrinsics and such.
*)
type value = Bool of bool | Num of int | Rune of char | String of string
type scope_entry = Pre of value | Val of value | Var of value option ref

module StringMap = Map.Make (String)

type scopes = scope_entry StringMap.t list
type ctrl = Brk | Ctn | Ret of value option | None of value option

exception Unreachable
exception InvalidBinopOperands of value option * value option * Lex.pos
exception InvalidUnaryOperand of value option * Lex.pos
exception InvalidIfCond of value option * Lex.pos
exception UseBeforeInitialization of string * Lex.pos
exception UninitializedPre of string * Lex.pos
exception UninitializedVal of string * Lex.pos
exception StmtUsedAsVal of Lex.pos
exception UnboundIdent of string * Lex.pos
exception Redeclaration of string * Lex.pos
exception ImmutableAssign of string * Lex.pos

let rec exec_expr { Parse.inner = expr; pos } scopes : ctrl * scopes =
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
          | Some (Bool b) -> None (Some (Bool (not b)))
          | _ -> raise (InvalidUnaryOperand (operand, pos)))
  | UnaryMins operand ->
      exec_uop operand (fun operand ->
          match operand with
          | Some (Num n) -> None (Some (Num (-n)))
          | _ -> raise (InvalidUnaryOperand (operand, pos)))
  | Eq binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Some (Bool b1), Some (Bool b2) -> Some (Bool (b1 = b2))
          | Some (Num n1), Some (Num n2) -> Some (Bool (n1 = n2))
          | Some (Rune r1), Some (Rune r2) -> Some (Bool (r1 = r2))
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Ne binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Some (Bool b1), Some (Bool b2) -> Some (Bool (b1 != b2))
          | Some (Num n1), Some (Num n2) -> Some (Bool (n1 != n2))
          | Some (Rune r1), Some (Rune r2) -> Some (Bool (r1 != r2))
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Le binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Some (Num n1), Some (Num n2) -> Some (Bool (n1 <= n2))
          | Some (Rune r1), Some (Rune r2) -> Some (Bool (r1 <= r2))
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Lt binop ->
      exec_binop binop (fun lhs rhs ->
          match (lhs, rhs) with
          | Some (Num n1), Some (Num n2) -> Some (Bool (n1 < n2))
          | Some (Rune r1), Some (Rune r2) -> Some (Bool (r1 < r2))
          | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Sum _variants -> raise TODO
  | Prod _fields -> raise TODO
  | Ident i -> (
      match List.find_map (fun scope -> StringMap.find_opt i scope) scopes with
      | Some (Pre value) | Some (Val value) -> (None (Some value), scopes)
      | Some (Var value_ref) -> (
          match !value_ref with
          | Some value -> (None (Some value), scopes)
          | None -> raise (UseBeforeInitialization (i, pos)))
      | None -> raise (UnboundIdent (i, pos)))
  | Block stmts -> exec_block stmts scopes
  | If { cond; if_branch; else_branch } -> (
      let ctrl, scopes = exec_expr cond scopes in
      match ctrl with
      | None (Some (Bool true)) -> exec_expr if_branch scopes
      | None (Some (Bool false)) -> (
          match else_branch with
          | Some else_branch -> exec_expr else_branch scopes
          | None -> (None None, scopes))
      | None cond -> raise (InvalidIfCond (cond, pos))
      | ctrl -> (ctrl, scopes))
  | ProcType { args = _; return_type = _ } -> raise TODO
  | Proc { type_' = { args = _; return_type = _ }; body = _ } -> raise TODO
  | Field { accessed = _; accessor = _ } -> raise TODO
  | Call { callee = _; args' = _ } -> raise TODO
  | Bool b -> (None (Some (Bool b)), scopes)
  | Num n -> (None (Some (Num n)), scopes)
  | Rune r -> (None (Some (Rune r)), scopes)
  | String s -> (None (Some (String s)), scopes)

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
      | Some (Num n1), Some (Num n2) -> Some (Num (op n1 n2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))

and exec_bool_binop pos scopes binop op =
  exec_binop pos scopes binop (fun lhs rhs ->
      match (lhs, rhs) with
      | Some (Bool b1), Some (Bool b2) -> Some (Bool (op b1 b2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))

and exec_uop scopes operand op =
  let ctrl, scopes = exec_expr operand scopes in
  match ctrl with None operand -> (op operand, scopes) | ctrl -> (ctrl, scopes)

and exec_block stmts scopes =
  match stmts with
  | [ stmt ] ->
      let ctrl, scopes = exec_stmt stmt (StringMap.empty :: scopes) in
      (ctrl, List.tl scopes)
  | stmts -> exec_nonsingle_block stmts (StringMap.empty :: scopes)

and exec_nonsingle_block stmts scopes =
  match stmts with
  | stmt :: stmts -> (
      let ctrl, scopes = exec_stmt stmt scopes in
      match ctrl with
      | None _ -> exec_nonsingle_block stmts scopes
      | ctrl -> (ctrl, scopes))
  | [] -> (None None, scopes)

(* scopes must be non-empty. *)
and exec_stmt { Parse.inner = stmt; pos } scopes =
  match stmt with
  | Parse.Brk -> (Brk, scopes)
  | Ctn -> (Ctn, scopes)
  | Ret value -> (
      match value with
      | Some value -> (
          let ctrl, scopes = exec_expr value scopes in
          match ctrl with
          | None (Some value) -> (Ret (Some value), scopes)
          | None None -> raise (StmtUsedAsVal pos)
          | ctrl -> (ctrl, scopes))
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
          | None (Some value) ->
              let entry =
                match kind with
                | Pre -> Pre value
                | Val -> Val value
                | Var -> Var (ref (Some value))
              in
              let scope = StringMap.add name entry scope in
              (None None, scope :: scopes)
          | None None -> raise (StmtUsedAsVal pos)
          | ctrl -> (ctrl, scopes))
      | Pre, None -> raise (UninitializedPre (name, pos))
      | Val, None -> raise (UninitializedVal (name, pos))
      | Var, None ->
          let scope = StringMap.add name (Var (ref Option.None)) scope in
          (None None, scope :: scopes))
  | Assign { assignee; value' } -> (
      match assignee with
      | Ident' i -> (
          match
            List.find_map (fun scope -> StringMap.find_opt i scope) scopes
          with
          | Some (Var value_ref) -> (
              let ctrl, scopes = exec_expr value' scopes in
              match ctrl with
              | None (Some value) ->
                  value_ref := Some value;
                  (None None, scopes)
              | None None -> raise (StmtUsedAsVal pos)
              | ctrl -> (ctrl, scopes))
          | Some _ -> raise (ImmutableAssign (i, pos))
          | None -> raise (UnboundIdent (i, pos)))
      | Field' _field -> raise TODO)
  | Loop body -> exec_loop body scopes
  | Expr expr ->
      let value, scopes = exec_expr { inner = expr; pos } scopes in
      (value, List.tl scopes)

and exec_loop body scopes =
  let ctrl, scopes = exec_expr body scopes in
  match ctrl with
  | Brk -> (None None, scopes)
  | Ret _ -> (ctrl, scopes)
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
  Some (Num 14) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false + true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 - 9" in
  Some (Num (-4)) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false - true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 * 9" in
  Some (Num 45) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false * true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 / 9" in
  Some (Num 0) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false / true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 % 9" in
  Some (Num 5) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false % true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "true && false" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "true && true" in
  Some (Bool true) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "5 && 9" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Some (Num 5), Some (Num 9), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "false || true" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "true || false" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "false || false" in
  Some (Bool false) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "5 || 9" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands (Some (Num 5), Some (Num 9), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "!false" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "!true" in
  Some (Bool false) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "!5" in
  let f () = easy_exec_expr ast in
  assert_raises (InvalidUnaryOperand (Some (Num 5), { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "-5" in
  Some (Num (-5)) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "-false" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidUnaryOperand (Some (Bool false), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "false == true" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "true == true" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "5 == 9" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "5 == 5" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' == 'q'" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' == 'r'" in
  Some (Bool true) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse {| "foo" == "bar" |} in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (String "foo"), Some (String "bar"), { row = 1; col = 2 }))
    f

let%test _ =
  let ast = parse "false != true" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "true != true" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "5 != 9" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "5 != 5" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' != 'q'" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' != 'r'" in
  Some (Bool false) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse {| "foo" != "bar" |} in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (String "foo"), Some (String "bar"), { row = 1; col = 2 }))
    f

let%test _ =
  let ast = parse "5 <= 5" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "9 <= 5" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' <= 'q'" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "'q' <= 'q'" in
  Some (Bool true) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false <= true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 < 5" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "5 < 9" in
  Some (Bool true) = easy_exec_expr ast

let%test _ =
  let ast = parse "'r' < 'r'" in
  Some (Bool false) = easy_exec_expr ast

let%test _ =
  let ast = parse "'q' <= 'r'" in
  Some (Bool true) = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "false < true" in
  let f () = easy_exec_expr ast in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "if true 5 else 9" in
  Some (Num 5) = easy_exec_expr ast

let%test _ =
  let ast = parse "if false 5 else 9" in
  Some (Num 9) = easy_exec_expr ast

let%test _ =
  let ast = parse "if false 5" in
  Option.None = easy_exec_expr ast

let%test_unit _ =
  let ast = parse "if 9 5 else 9" in
  let f () = easy_exec_expr ast in
  assert_raises (InvalidIfCond (Some (Num 9), { row = 1; col = 1 })) f
