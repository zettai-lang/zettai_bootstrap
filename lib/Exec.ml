exception TODO

module StringMap = Map.Make (String)

type value =
  | Num of int
  | Rune of char
  | SumVariant of sum_variant
  | Prod of prod
  | Proc of (prod -> Lex.pos -> value)
  | Type of type'

and scope_entry = Mut of value option ref | Val of value
and prod_field = { name : string; entry : scope_entry }
and prod = prod_field list
and sum_variant = { type' : sum_type; disc : int; field : value option }

(* TODO: add the rest of the variants and typecheck everything *)
and type' = Num' | Rune' | Sum of sum_type | Proc' of proc_type
and sum_type = sum_variant_type list

and sum_variant_type = {
  name' : string;
  disc' : int;
  field_type : type' option;
}

and prod_field_type = { kind : Parse.kind; name'' : string; type'' : type' }
and proc_type = { arg_types : prod_field_type list; return_type : type' }

let scope_entry_from_kind kind value =
  match kind with Parse.Mut -> Mut (ref (Some value)) | Val -> Val value

exception UseBeforeInitialization of string * Lex.pos

let () =
  Printexc.register_printer (function
    | UseBeforeInitialization (name, { path; row; col }) ->
        Some
          (Printf.sprintf "%s:%d:%d: use of \"%s\" before initialization" path
             row col name)
    | _ -> None)

let value_from_scope_entry name pos = function
  | Mut value_ref -> (
      match !value_ref with
      | Some value -> value
      | None -> raise (UseBeforeInitialization (name, pos)))
  | Val value -> value

(* TODO: replace this with a general typecheck error *)
exception ValueAsType of value * Lex.pos

let expect_type value pos =
  match value with Type t -> t | _ -> raise (ValueAsType (value, pos))

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
    | NumAsArgumentName { path; row; col } ->
        Some
          (Printf.sprintf "%s:%d:%d: number specified as argument name" path row
             col)
    | _ -> None)

exception ValueAsArgument of Lex.pos

let () =
  Printexc.register_printer (function
    | ValueAsArgument { path; row; col } ->
        Some
          (Printf.sprintf "%s:%d:%d: value specified in function declaration"
             path row col)
    | _ -> None)

exception MutArgument of Lex.pos

let () =
  Printexc.register_printer (function
    | MutArgument { path; row; col } ->
        Some (Printf.sprintf "%s:%d:%d: argument specified as mut" path row col)
    | _ -> None)

let rec args_names = function
  | [] -> []
  | {
      Parse.inner =
        Parse.Decl' { kind'; name_or_count = { inner = Ident'' name; _ }; _ };
      pos;
    }
    :: fields ->
      let () =
        match kind' with Some Parse.Mut -> raise (MutArgument pos) | _ -> ()
      in
      name :: args_names fields
  | { inner = Decl' { name_or_count = { inner = Num'' _; pos }; _ }; _ } :: _ ->
      raise (NumAsArgumentName pos)
  | { inner = Value' _; pos } :: _ -> raise (ValueAsArgument pos)

exception InvalidBinopOperands of value * value * Lex.pos
exception InvalidUnaryOperand of value * Lex.pos
exception InvalidIfCond of value * Lex.pos
exception UninitializedVal of string * Lex.pos
exception UnboundIdent of string * Lex.pos

let () =
  Printexc.register_printer (function
    | UnboundIdent (name, { path; row; col }) ->
        Some
          (Printf.sprintf "%s:%d:%d: unbound ident: \"%s\"" path row col name)
    | _ -> None)

exception Redeclaration of string * Lex.pos
exception ImmutableAssign of Parse.ident_or_field * Lex.pos
exception InvalidAccess of value * Lex.pos
exception InvalidField of string * Lex.pos
exception InvalidCallArgs of string list * prod * Lex.pos
exception InvalidCallee of value * Lex.pos
exception UnexpectedCtrl of Lex.pos

let bool_type : sum_type =
  [
    { name' = "False"; disc' = 0; field_type = None };
    { name' = "True"; disc' = 1; field_type = None };
  ]

let bool_from_bool b =
  SumVariant { type' = bool_type; disc = (if b then 1 else 0); field = None }

let is_bool { type'; _ } = type' == bool_type
let bool_not { disc; _ } = bool_from_bool (disc = 0)

exception ProcTypeWithoutReturn of Lex.pos
exception Unreachable

let rec exec_expr { Parse.inner = expr; pos } scopes =
  let exec_binop = exec_binop pos scopes in
  let exec_uop = exec_uop scopes in
  let exec_num_binop = exec_num_binop pos scopes in
  let exec_bool_binop = exec_bool_binop pos scopes in
  let rec eq lhs rhs =
    match (lhs, rhs) with
    | SumVariant v1, SumVariant v2 -> (
        v1.type' == v2.type' && v1.disc = v2.disc
        &&
        match (v1.field, v2.field) with
        | Some f1, Some f2 -> eq f1 f2
        | None, None -> true
        | _ -> raise Unreachable)
    | Num n1, Num n2 -> n1 = n2
    | Rune r1, Rune r2 -> r1 = r2
    | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs, pos))
  in
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
  | Eq binop -> exec_binop binop (fun lhs rhs -> bool_from_bool (eq lhs rhs))
  | Ne binop ->
      exec_binop binop (fun lhs rhs -> bool_from_bool (not (eq lhs rhs)))
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
  | Sum variants -> exec_sum variants scopes
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
  | ProcType { args = { inner = args; _ }; return_type = Some return_type } ->
      let ctrl_of_arg_types = exec_arg_types args scopes in
      map_ctrl_of
        (fun arg_types ->
          let return_type_ctrl = exec_expr return_type scopes in
          map_ctrl_of
            (fun return_type_val ->
              let return_type = expect_type return_type_val return_type.pos in
              None (Type (Proc' { arg_types; return_type })))
            return_type_ctrl)
        ctrl_of_arg_types
  | ProcType { return_type = None; _ } -> raise (ProcTypeWithoutReturn pos)
  | Proc { type_' = { args = { inner = args; _ }; _ }; body } ->
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
          | Type (Sum type') -> (
              match
                List.find_opt (fun { name'; _ } -> name' = accessor) type'
              with
              | Some { disc' = disc; field_type = None; _ } ->
                  None (SumVariant { type'; disc; field = None })
              | Some { disc' = disc; field_type = Some _; _ } ->
                  None
                    (Proc
                       (fun fields pos ->
                         match fields with
                         | [ { name = "value"; entry } ] ->
                             let value =
                               value_from_scope_entry "value" pos entry
                             in
                             SumVariant { type'; disc; field = Some value }
                         | _ ->
                             raise (InvalidCallArgs ([ "value" ], fields, pos))))
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

and exec_sum variants scopes =
  let ctrl_of_variants =
    List.fold_left
      (fun ctrl { Parse.inner = { Parse.name'; value''' }; _ } ->
        map_ctrl_of
          (fun variants ->
            let disc' = Oo.id (object end) in
            match value''' with
            | Some value ->
                let field_type_ctrl = exec_expr value scopes in
                map_ctrl_of
                  (fun field_type ->
                    let field_type = Some (expect_type field_type value.pos) in
                    None (variants @ [ { name'; disc'; field_type } ]))
                  field_type_ctrl
            | None -> None (variants @ [ { name'; disc'; field_type = None } ]))
          ctrl)
      (None []) variants
  in
  map_ctrl_of (fun variants -> None (Type (Sum variants))) ctrl_of_variants

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

and exec_arg_types args scopes =
  let _, ctrl =
    List.fold_left
      (fun (prev_kind, ctrl) { Parse.inner = arg; pos } ->
        match ctrl with
        | None args -> (
            match arg with
            | Parse.Decl'
                {
                  kind';
                  name_or_count = { inner = Ident'' name''; _ };
                  type_'' = Some type_;
                  value'' = None;
                } -> (
                let kind = Option.value kind' ~default:prev_kind in
                let ctrl = exec_expr type_ scopes in
                let () =
                  match
                    List.find_opt
                      (fun { name'' = existing_name; _ } ->
                        existing_name = name'')
                      args
                  with
                  | Some { name''; _ } -> raise (Redeclaration (name'', pos))
                  | None -> ()
                in
                match ctrl with
                | None type_val ->
                    let type'' = expect_type type_val type_.pos in
                    (kind, None (args @ [ { kind; name''; type'' } ]))
                | Brk pos -> (kind, Brk pos)
                | Ctn pos -> (kind, Ctn pos)
                | Ret (value, pos) -> (kind, Ret (value, pos)))
            | _ -> raise TODO)
        | Brk pos -> (prev_kind, Brk pos)
        | Ctn pos -> (prev_kind, Ctn pos)
        | Ret (value, pos) -> (prev_kind, Ret (value, pos)))
      (Parse.Val, None []) args
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
  | Decl { kind = { inner = kind; _ }; name = { inner = name; _ }; value; _ }
    -> (
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

let rec stringify value =
  let indent text = String.split_on_char '\n' text |> String.concat "\n  " in
  match value with
  | Num n -> string_of_int n
  | Rune r -> "'" ^ Char.escaped r ^ "'"
  | SumVariant { type'; disc; field } ->
      let name =
        match List.find_opt (fun { disc'; _ } -> disc' = disc) type' with
        | None -> raise Unreachable
        | Some { name'; _ } -> name'
      in
      let field_string =
        Option.map (fun field -> "(" ^ (stringify field |> indent) ^ ")") field
      in
      name ^ Option.value field_string ~default:""
  | Prod [] -> "()"
  | Prod fields ->
      let field_strings =
        List.map
          (fun { name; entry } ->
            let entry_string =
              match entry with
              | Mut value_ref -> (
                  match !value_ref with
                  | Some value -> stringify value |> indent
                  | None -> "(uninitialized)")
              | Val value -> stringify value |> indent
            in
            name ^ " = " ^ entry_string ^ ",")
          fields
      in
      let fields_string = String.concat "\n  " field_strings in
      "(\n  " ^ fields_string ^ "\n)"
  | Proc _ -> "proc(...) { ... }"
  | Type t -> (
      match t with
      | Num' -> "Num"
      | Rune' -> "Rune"
      | Sum [] -> "[]"
      | Sum variants ->
          let variant_strings =
            List.map
              (fun { name'; field_type; _ } ->
                let field_type_string =
                  Option.map
                    (fun field_type ->
                      "(" ^ (stringify (Type field_type) |> indent) ^ ")")
                    field_type
                in
                name' ^ Option.value field_type_string ~default:"" ^ ",")
              variants
          in
          let variants_string = String.concat "\n  " variant_strings in
          "[\n  " ^ variants_string ^ "\n]"
      | Proc' { arg_types; return_type } ->
          let arg_types_string =
            match arg_types with
            | [] -> "()"
            | _ ->
                let arg_type_strings =
                  List.map
                    (fun { kind; name''; type'' } ->
                      let kind_string =
                        match kind with Parse.Mut -> "mut" | Val -> "val"
                      in
                      let type_string = stringify (Type type'') in
                      kind_string ^ " " ^ name'' ^ ": " ^ type_string ^ ",")
                    arg_types
                in
                "(\n  " ^ String.concat "\n  " arg_type_strings ^ "\n)"
          in
          let return_type_string = stringify (Type return_type) in
          "proc" ^ arg_types_string ^ ": " ^ return_type_string)

let%expect_test _ =
  stringify (Num 5) |> print_endline;
  [%expect "5"]

let%expect_test _ =
  stringify (Rune 'a') |> print_endline;
  [%expect "'a'"]

let%expect_test _ =
  stringify (Rune '\r') |> print_endline;
  [%expect "'\\r'"]

let%expect_test _ =
  stringify (SumVariant { type' = bool_type; disc = 1; field = None })
  |> print_endline;
  [%expect "True"]

let%expect_test _ =
  stringify
    (SumVariant
       {
         type' =
           [
             { name' = "Bar"; disc' = 0; field_type = None };
             { name' = "Baz"; disc' = 9; field_type = Some Rune' };
           ];
         disc = 9;
         field = Some (Rune '\n');
       })
  |> print_endline;
  [%expect "Baz('\\n')"]

let%expect_test _ =
  stringify (Prod []) |> print_endline;
  [%expect "()"]

let%expect_test _ =
  stringify (Prod [ { name = "foo"; entry = Val (Num 9) } ]) |> print_endline;
  [%expect {|
(
  foo = 9,
)
|}]

let%expect_test _ =
  stringify
    (Prod
       [
         { name = "foo"; entry = Val (Num 9) };
         { name = "bar"; entry = Mut (ref (Some (Rune 'r'))) };
         { name = "baz"; entry = Mut (ref Option.None) };
       ])
  |> print_endline;
  [%expect {|
(
  foo = 9,
  bar = 'r',
  baz = (uninitialized),
)
|}]

let%expect_test _ =
  stringify
    (Prod
       [
         {
           name = "foo";
           entry =
             Val
               (Prod
                  [
                    {
                      name = "bar";
                      entry =
                        Val (Prod [ { name = "baz"; entry = Val (Prod []) } ]);
                    };
                  ]);
         };
       ])
  |> print_endline;
  [%expect {|
(
  foo = (
    bar = (
      baz = (),
    ),
  ),
)
|}]

let%expect_test _ =
  stringify (Proc (fun _ _ -> unit_val)) |> print_endline;
  [%expect "proc(...) { ... }"]

let%expect_test _ =
  stringify (Type Num') |> print_endline;
  [%expect "Num"]

let%expect_test _ =
  stringify (Type Rune') |> print_endline;
  [%expect "Rune"]

let%expect_test _ =
  stringify (Type (Sum [])) |> print_endline;
  [%expect "[]"]

let%expect_test _ =
  stringify (Type (Sum [ { name' = "Foo"; disc' = 0; field_type = None } ]))
  |> print_endline;
  [%expect {|
[
  Foo,
]
|}]

let%expect_test _ =
  stringify
    (Type (Sum [ { name' = "Foo"; disc' = 0; field_type = Some Rune' } ]))
  |> print_endline;
  [%expect {|
[
  Foo(Rune),
]
|}]

let%expect_test _ =
  stringify
    (Type
       (Sum
          [
            { name' = "Foo"; disc' = 0; field_type = Some Rune' };
            { name' = "Bar"; disc' = 1; field_type = None };
            { name' = "Baz"; disc' = 2; field_type = Some Num' };
          ]))
  |> print_endline;
  [%expect {|
[
  Foo(Rune),
  Bar,
  Baz(Num),
]
|}]

let%expect_test _ =
  stringify (Type (Proc' { arg_types = []; return_type = Rune' }))
  |> print_endline;
  [%expect "proc(): Rune"]

let%expect_test _ =
  stringify
    (Type
       (Proc'
          {
            arg_types = [ { kind = Parse.Val; name'' = "foo"; type'' = Num' } ];
            return_type = Sum [];
          }))
  |> print_endline;
  [%expect {|
  proc(
    val foo: Num,
  ): []
|}]

let%expect_test _ =
  stringify
    (Type
       (Proc'
          {
            arg_types =
              [
                { kind = Parse.Val; name'' = "foo"; type'' = Num' };
                { kind = Mut; name'' = "bar"; type'' = Rune' };
              ];
            return_type = Sum [];
          }))
  |> print_endline;
  [%expect {|
  proc(
    val foo: Num,
    mut bar: Rune,
  ): []
|}]

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
                   let () = stringify value |> print_endline in
                   unit_val
               | _ -> raise (InvalidCallArgs ([ "value" ], fields, pos))));
    };
  ]

let builtins =
  let builtins = StringMap.empty in
  let builtins = StringMap.add "False" (Val (bool_from_bool false)) builtins in
  let builtins = StringMap.add "True" (Val (bool_from_bool true)) builtins in
  let builtins = StringMap.add "Num" (Val (Type Num')) builtins in
  let builtins = StringMap.add "Rune" (Val (Type Rune')) builtins in
  StringMap.add "intrinsics" (Val (Prod intrinsics)) builtins

let exec_ast ast =
  let ctrl = exec_expr ast [ ref builtins ] in
  match ctrl with
  | None value -> value
  | Brk pos | Ctn pos | Ret (_, pos) -> raise (UnexpectedCtrl pos)

exception ExpectedProc

let exec path =
  let text = Core.In_channel.read_lines path |> String.concat "\n" in
  let ast = Parse.parse text path in
  let _ =
    match exec_ast ast with
    | Proc f -> f [] { path; row = 0; col = 0 }
    | _ -> raise ExpectedProc
  in
  ()

let assert_raises = OUnit2.assert_raises
let parse = Parse.parse

let%test _ =
  let ast = parse "5 + 9" "test.zt" in
  Num 14 = exec_ast ast

let%test_unit _ =
  let ast = parse "5 == True" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       (Num 5, bool_from_bool true, { path = "test.zt"; row = 1; col = 1 }))
    f

let%test_unit _ =
  let ast = parse "False + True" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       ( bool_from_bool false,
         bool_from_bool true,
         { path = "test.zt"; row = 1; col = 1 } ))
    f

let%test _ =
  let ast = parse "5 - 9" "test.zt" in
  Num (-4) = exec_ast ast

let%test_unit _ =
  let ast = parse "False - True" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       ( bool_from_bool false,
         bool_from_bool true,
         { path = "test.zt"; row = 1; col = 1 } ))
    f

let%test _ =
  let ast = parse "5 * 9" "test.zt" in
  Num 45 = exec_ast ast

let%test_unit _ =
  let ast = parse "False * True" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       ( bool_from_bool false,
         bool_from_bool true,
         { path = "test.zt"; row = 1; col = 1 } ))
    f

let%test _ =
  let ast = parse "5 / 9" "test.zt" in
  Num 0 = exec_ast ast

let%test_unit _ =
  let ast = parse "False / True" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       ( bool_from_bool false,
         bool_from_bool true,
         { path = "test.zt"; row = 1; col = 1 } ))
    f

let%test _ =
  let ast = parse "5 % 9" "test.zt" in
  Num 5 = exec_ast ast

let%test_unit _ =
  let ast = parse "False % True" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       ( bool_from_bool false,
         bool_from_bool true,
         { path = "test.zt"; row = 1; col = 1 } ))
    f

let%test _ =
  let ast = parse "True && False" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "True && True" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "5 && 9" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Num 5, Num 9, { path = "test.zt"; row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "False || True" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "True || False" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "False || False" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "5 || 9" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (Num 5, Num 9, { path = "test.zt"; row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "!False" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "!True" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "!5" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidUnaryOperand (Num 5, { path = "test.zt"; row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "-5" "test.zt" in
  Num (-5) = exec_ast ast

let%test_unit _ =
  let ast = parse "-False" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidUnaryOperand
       (bool_from_bool false, { path = "test.zt"; row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "False == True" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "True == True" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "5 == 9" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "5 == 5" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' == 'q'" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' == 'r'" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "False != True" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "True != True" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "5 != 9" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "5 != 5" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' != 'q'" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' != 'r'" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "5 <= 5" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "9 <= 5" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'r' <= 'q'" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'q' <= 'q'" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "False <= True" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       ( bool_from_bool false,
         bool_from_bool true,
         { path = "test.zt"; row = 1; col = 1 } ))
    f

let%test _ =
  let ast = parse "5 < 5" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "5 < 9" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "'r' < 'r'" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "'q' <= 'r'" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "False < True" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands
       ( bool_from_bool false,
         bool_from_bool true,
         { path = "test.zt"; row = 1; col = 1 } ))
    f

let%test _ =
  let ast = parse "if True 5 else 9" "test.zt" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "if False 5 else 9" "test.zt" in
  Num 9 = exec_ast ast

let%test _ =
  let ast = parse "if False 5" "test.zt" in
  unit_val = exec_ast ast

let%test_unit _ =
  let ast = parse "if 9 5 else 9" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidIfCond (Num 9, { path = "test.zt"; row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "()" "test.zt" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9)" "test.zt" in
  Prod [ { name = "i"; entry = Val (Num 9) } ] = exec_ast ast

let%test_unit _ =
  let ast = parse "(val i = 9, val i = 9)" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { path = "test.zt"; row = 1; col = 13 })) f

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = True)" "test.zt" in
  Prod
    [
      { name = "i"; entry = Val (Num 9) };
      { name = "j"; entry = Val (Rune 'a') };
      { name = "k"; entry = Mut (ref (Some (bool_from_bool true))) };
    ]
  = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9).i" "test.zt" in
  Num 9 = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = True).j" "test.zt" in
  Rune 'a' = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = True).k" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = True).k" "test.zt" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "().i" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (InvalidField ("i", { path = "test.zt"; row = 1; col = 4 })) f

let%test_unit _ =
  let ast = parse "1.i" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidAccess (Num 1, { path = "test.zt"; row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "[]" "test.zt" in
  match exec_ast ast with Type (Sum []) -> true | _ -> false

let%test _ =
  let ast = parse "[Red, Green(Num), Blue(Rune)]" "test.zt" in
  match exec_ast ast with
  | Type
      (Sum
        [
          { name' = "Red"; field_type = None; _ };
          { name' = "Green"; field_type = Some Num'; _ };
          { name' = "Blue"; field_type = Some Rune'; _ };
        ]) ->
      true
  | _ -> false

let%test _ =
  let ast = parse "[Red].Red" "test.zt" in
  match exec_ast ast with SumVariant { field = None; _ } -> true | _ -> false

let%test _ =
  let ast = parse "[Green(Num)].Green(value = 5)" "test.zt" in
  match exec_ast ast with
  | SumVariant { field = Some (Num 5); _ } -> true
  | _ -> false

let%test_unit _ =
  let ast = parse "[Green(Num)].Green(foo = 5)" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidCallArgs
       ( [ "value" ],
         [ { name = "foo"; entry = Val (Num 5) } ],
         { path = "test.zt"; row = 1; col = 19 } ))
    f

let%test_unit _ =
  let ast = parse "[].Blue" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidField ("Blue", { path = "test.zt"; row = 1; col = 4 }))
    f

let%test _ =
  (*
  The two sums are separate, so the variants aren't equal though they happen to
  have the same names
  *)
  let ast = parse "[Red].Red == [Red].Red" "test.zt" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    proc() {
      val sum = [Red, Green, Blue]
      ret sum.Green == sum.Green
    }()
  |}
      "test.zt"
  in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    proc() {
      val sum = [Red, Green(Num), Blue]
      ret sum.Green(value = 5) == sum.Green(value = 5)
    }()
  |}
      "test.zt"
  in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    proc() {
      val sum = [Red, Green(Num), Blue]
      ret sum.Green(value = 5) == sum.Green(value = 9)
    }()
  |}
      "test.zt"
  in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    proc() {
      val sum = [Red, Green(Num), Blue(Num)]
      ret sum.Green(value = 5) == sum.Blue(value = 5)
    }()
  |}
      "test.zt"
  in
  bool_from_bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "[].Blue" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidField ("Blue", { path = "test.zt"; row = 1; col = 4 }))
    f

let%test_unit _ =
  let ast = parse "[Blue(5)]" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (ValueAsType (Num 5, { path = "test.zt"; row = 1; col = 7 })) f

let%test _ =
  let ast = parse "{ proc() { } }()" "test.zt" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "{ proc(val i: Nat) { i + 1 } }(val i = 2)" "test.zt" in
  Num 3 = exec_ast ast

let%test _ =
  let ast =
    parse "{ proc(val i: Nat, val j: Nat) { i * j } }(val i = 2, val j = 9)"
      "test.zt"
  in
  Num 18 = exec_ast ast

let%test _ =
  let ast =
    parse "{ proc(val i, j: Nat) { i * j } }(val i = 2, val j = 9)" "test.zt"
  in
  Num 18 = exec_ast ast

let%test_unit _ =
  let ast = parse "{ proc(val i: Nat) { i } }(val j = 2)" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidCallArgs
       ( [ "i" ],
         [ { name = "j"; entry = Val (Num 2) } ],
         { path = "test.zt"; row = 1; col = 27 } ))
    f

let%test_unit _ =
  let ast = parse "{ proc(val i: Nat) { i } }()" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidCallArgs ([ "i" ], [], { path = "test.zt"; row = 1; col = 27 }))
    f

let%test_unit _ =
  let ast = parse "proc(mut i: Nat) { i }" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (MutArgument { path = "test.zt"; row = 1; col = 6 }) f

let%test_unit _ =
  let ast = parse "proc(val 5: Nat) { }" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (NumAsArgumentName { path = "test.zt"; row = 1; col = 10 }) f

let%test_unit _ =
  let ast = parse "proc('a') { }" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (ValueAsArgument { path = "test.zt"; row = 1; col = 6 }) f

let%test_unit _ =
  let ast = parse "{ proc() { foo } }()" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (UnboundIdent ("foo", { path = "test.zt"; row = 1; col = 12 }))
    f

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
      "test.zt"
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
      "test.zt"
  in
  let f () = exec_ast ast in
  assert_raises
    (UseBeforeInitialization ("i", { path = "test.zt"; row = 5; col = 13 }))
    f

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
      "test.zt"
  in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { loop { ret 'a' } } }()" "test.zt" in
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
      "test.zt"
  in
  Num 9 = exec_ast ast

let%test_unit _ =
  let ast = parse "{ proc() { brk } }()" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { path = "test.zt"; row = 1; col = 12 }) f

let%test_unit _ =
  let ast = parse "{ proc() { ctn } }()" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { path = "test.zt"; row = 1; col = 12 }) f

let%test _ =
  let ast = parse "{ proc() { { ret 5 }.foo } }()" "test.zt" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { { ret 5 }() } }()" "test.zt" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { { ret 5 } + 1 } }()" "test.zt" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { 1 + { ret 5 } } }()" "test.zt" in
  Num 5 = exec_ast ast

let%test_unit _ =
  let ast = parse "1()" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidCallee (Num 1, { path = "test.zt"; row = 1; col = 1 }))
    f

let%test _ =
  let ast = parse "{ proc() { mut i } }()" "test.zt" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "{ proc() { ret } }()" "test.zt" in
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
      "test.zt"
  in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { path = "test.zt"; row = 5; col = 9 })) f

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
      "test.zt"
  in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { path = "test.zt"; row = 5; col = 9 })) f

let%test_unit _ =
  let ast = parse "{ proc() { val i } }()" "test.zt" in
  let f () = exec_ast ast in
  assert_raises
    (UninitializedVal ("i", { path = "test.zt"; row = 1; col = 12 }))
    f

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
      "test.zt"
  in
  let f () = exec_ast ast in
  assert_raises
    (ImmutableAssign (Ident' "i", { path = "test.zt"; row = 5; col = 9 }))
    f

let%test_unit _ =
  let ast =
    parse {|
    {
      proc() {
        i = 1
      }
    }()
  |} "test.zt"
  in
  let f () = exec_ast ast in
  assert_raises (UnboundIdent ("i", { path = "test.zt"; row = 4; col = 9 })) f

let%test_unit _ =
  let ast = parse "{ brk }" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { path = "test.zt"; row = 1; col = 3 }) f

let%test_unit _ =
  let ast = parse "{ ctn }" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { path = "test.zt"; row = 1; col = 3 }) f

let%test_unit _ =
  let ast = parse "{ ret }" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (UnexpectedCtrl { path = "test.zt"; row = 1; col = 3 }) f

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
      "test.zt"
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
      "test.zt"
  in
  let f () = exec_ast ast in
  assert_raises
    (InvalidField ("bogus", { path = "test.zt"; row = 5; col = 11 }))
    f

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
      "test.zt"
  in
  let f () = exec_ast ast in
  assert_raises
    (InvalidAccess (Num 1, { path = "test.zt"; row = 5; col = 9 }))
    f

let%test _ =
  let ast = parse "proc(): Num" "test.zt" in
  Type (Proc' { arg_types = []; return_type = Num' }) = exec_ast ast

let%test _ =
  let ast = parse "proc(foo: Num): Num" "test.zt" in
  Type
    (Proc'
       {
         arg_types = [ { kind = Parse.Val; name'' = "foo"; type'' = Num' } ];
         return_type = Num';
       })
  = exec_ast ast

let%test _ =
  let ast = parse "proc(mut foo: Num, baz: Rune): Num" "test.zt" in
  Type
    (Proc'
       {
         arg_types =
           [
             { kind = Parse.Mut; name'' = "foo"; type'' = Num' };
             { kind = Mut; name'' = "baz"; type'' = Rune' };
           ];
         return_type = Num';
       })
  = exec_ast ast

let%test_unit _ =
  let ast = parse "proc(i: Num, i: Num): Num" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (Redeclaration ("i", { path = "test.zt"; row = 1; col = 14 })) f

let%test_unit _ =
  let ast = parse "proc(i: Num)" "test.zt" in
  let f () = exec_ast ast in
  assert_raises (ProcTypeWithoutReturn { path = "test.zt"; row = 1; col = 1 }) f
