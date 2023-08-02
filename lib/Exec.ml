exception TODO

(*
  TODO: strings aren't really primitive values... but we do need to be able to
  represent literals somehow... might have to figure out how this works with
  intrinsics and such.
*)
type value = Bool of bool | Num of int | Rune of char | String of string

exception InvalidBinopOperands of value option * value option * Lex.pos
exception InvalidUnaryOperand of value option * Lex.pos
exception InvalidIfCond of value option * Lex.pos

let rec exec_ast { Parse.inner = expr; pos } args debug =
  match expr with
  | Parse.Plus { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Num n1), Some (Num n2) -> Some (Num (n1 + n2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Mins { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Num n1), Some (Num n2) -> Some (Num (n1 - n2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Astr { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Num n1), Some (Num n2) -> Some (Num (n1 * n2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Slsh { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Num n1), Some (Num n2) -> Some (Num (n1 / n2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Perc { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Num n1), Some (Num n2) -> Some (Num (n1 mod n2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | And { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Bool b1), Some (Bool b2) -> Some (Bool (b1 && b2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Or { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Bool b1), Some (Bool b2) -> Some (Bool (b1 || b2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Not operand -> (
      let operand = exec_ast operand args debug in
      match operand with
      | Some (Bool b) -> Some (Bool (not b))
      | _ -> raise (InvalidUnaryOperand (operand, pos)))
  | UnaryMins operand -> (
      let operand = exec_ast operand args debug in
      match operand with
      | Some (Num n) -> Some (Num (-n))
      | _ -> raise (InvalidUnaryOperand (operand, pos)))
  | Eq { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Bool b1), Some (Bool b2) -> Some (Bool (b1 = b2))
      | Some (Num n1), Some (Num n2) -> Some (Bool (n1 = n2))
      | Some (Rune r1), Some (Rune r2) -> Some (Bool (r1 = r2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Ne { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Bool b1), Some (Bool b2) -> Some (Bool (b1 != b2))
      | Some (Num n1), Some (Num n2) -> Some (Bool (n1 != n2))
      | Some (Rune r1), Some (Rune r2) -> Some (Bool (r1 != r2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Le { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Num n1), Some (Num n2) -> Some (Bool (n1 <= n2))
      | Some (Rune r1), Some (Rune r2) -> Some (Bool (r1 <= r2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Lt { lhs; rhs } -> (
      let lhs = exec_ast { inner = lhs; pos } args debug in
      let rhs = exec_ast rhs args debug in
      match (lhs, rhs) with
      | Some (Num n1), Some (Num n2) -> Some (Bool (n1 < n2))
      | Some (Rune r1), Some (Rune r2) -> Some (Bool (r1 < r2))
      | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos)))
  | Sum _variants -> raise TODO
  | Prod _fields -> raise TODO
  | Ident _i -> raise TODO
  | Block _stmts -> raise TODO
  | If { cond; if_branch; else_branch } -> (
      let cond = exec_ast cond args debug in
      match cond with
      | Some (Bool b) -> (
          if b then exec_ast if_branch args debug
          else
            match else_branch with
            | Some else_branch -> exec_ast else_branch args debug
            | None -> None)
      | cond -> raise (InvalidIfCond (cond, pos)))
  | ProcType { args = _; return_type = _ } -> raise TODO
  | Proc { type_' = { args = _; return_type = _ }; body = _ } -> raise TODO
  | Field { accessed = _; accessor = _ } -> raise TODO
  | Call { callee = _; args' = _ } -> raise TODO
  | Bool b -> Some (Bool b)
  | Num n -> Some (Num n)
  | Rune r -> Some (Rune r)
  | String s -> Some (String s)

let exec path args debug =
  let text = Core.In_channel.read_lines path in
  let ast = String.concat "\n" text |> Parse.parse in
  let _ = exec_ast ast args debug in
  ()

let assert_raises = OUnit2.assert_raises
let parse = Parse.parse

let%test _ =
  let ast = parse "5 + 9" in
  Some (Num 14) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "false + true" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 - 9" in
  Some (Num (-4)) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "false - true" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 * 9" in
  Some (Num 45) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "false * true" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 / 9" in
  Some (Num 0) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "false / true" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 % 9" in
  Some (Num 5) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "false % true" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "true && false" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "true && true" in
  Some (Bool true) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "5 && 9" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands (Some (Num 5), Some (Num 9), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "false || true" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "true || false" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "false || false" in
  Some (Bool false) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "5 || 9" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands (Some (Num 5), Some (Num 9), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "!false" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "!true" in
  Some (Bool false) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "!5" in
  let f () = exec_ast ast [] false in
  assert_raises (InvalidUnaryOperand (Some (Num 5), { row = 1; col = 1 })) f

let%test _ =
  let ast = parse "-5" in
  Some (Num (-5)) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "-false" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidUnaryOperand (Some (Bool false), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "false == true" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "true == true" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "5 == 9" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "5 == 5" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "'r' == 'q'" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "'r' == 'r'" in
  Some (Bool true) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse {| "foo" == "bar" |} in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (String "foo"), Some (String "bar"), { row = 1; col = 2 }))
    f

let%test _ =
  let ast = parse "false != true" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "true != true" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "5 != 9" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "5 != 5" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "'r' != 'q'" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "'r' != 'r'" in
  Some (Bool false) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse {| "foo" != "bar" |} in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (String "foo"), Some (String "bar"), { row = 1; col = 2 }))
    f

let%test _ =
  let ast = parse "5 <= 5" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "9 <= 5" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "'r' <= 'q'" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "'q' <= 'q'" in
  Some (Bool true) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "false <= true" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "5 < 5" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "5 < 9" in
  Some (Bool true) = exec_ast ast [] false

let%test _ =
  let ast = parse "'r' < 'r'" in
  Some (Bool false) = exec_ast ast [] false

let%test _ =
  let ast = parse "'q' <= 'r'" in
  Some (Bool true) = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "false < true" in
  let f () = exec_ast ast [] false in
  assert_raises
    (InvalidBinopOperands
       (Some (Bool false), Some (Bool true), { row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "if true 5 else 9" in
  Some (Num 5) = exec_ast ast [] false

let%test _ =
  let ast = parse "if false 5 else 9" in
  Some (Num 9) = exec_ast ast [] false

let%test _ =
  let ast = parse "if false 5" in
  None = exec_ast ast [] false

let%test_unit _ =
  let ast = parse "if 9 5 else 9" in
  let f () = exec_ast ast [] false in
  assert_raises (InvalidIfCond (Some (Num 9), { row = 1; col = 1 })) f
