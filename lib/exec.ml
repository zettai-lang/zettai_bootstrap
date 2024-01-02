open Util

exception TODO

module StringMap = Map.Make (String)

type value =
  | Num of int
  | Rune of char
  | SumVariant of sum_variant
  | Prod of prod
  | Proc of (prod -> value)
  | Type of type'

and scope_entry = Mut of value option ref | Val of value
and prod_field = { name : string option; entry : scope_entry }
and prod = prod_field list
and sum_variant = { type' : sum_type; disc : int; field : value option }

(* TODO: typecheck everything *)
and type' =
  | Num
  | Rune
  | Sum of sum_type
  | Prod of prod_field_type list
  | Proc of proc_type

and sum_type = sum_variant_type list
and sum_variant_type = { name : string; disc : int; field_type : type' option }
and prod_field_type = { kind : Parse.kind; name : string; type' : type' }
and proc_type = { arg_types : prod_field_type list; return_type : type' }

let scope_entry value = function
  | Parse.Mut -> Mut (ref (Some value))
  | Val -> Val value

exception UseBeforeInitialization of string

let () =
  Printexc.register_printer (function
    | UseBeforeInitialization name ->
        Some (Printf.sprintf "use of \"%s\" before initialization" name)
    | _ -> None)

let value_of_scope_entry name = function
  | Mut value_ref ->
      get_or_else !value_ref (fun () -> raise (UseBeforeInitialization name))
  | Val value -> value

(* TODO: replace this with a general typecheck error *)
exception ValueAsType of value

let expect_type = function
  | Type t -> t
  | invalid -> raise (ValueAsType invalid)

let unit_val = Prod []

type 'a ctrl = Brk | Ctn | Ret of value option | None of 'a

let return a = None a

let ( >>= ) ctrl f =
  match ctrl with
  | Brk -> Brk
  | Ctn -> Ctn
  | Ret value -> Ret value
  | None a -> f a

let ( let* ) = ( >>= )

exception NumAsArgumentName

let () =
  Printexc.register_printer (function
    | NumAsArgumentName ->
        Some (Printf.sprintf "number specified as argument name")
    | _ -> None)

exception ValueAsArgument

let () =
  Printexc.register_printer (function
    | ValueAsArgument ->
        Some (Printf.sprintf "value specified in function declaration")
    | _ -> None)

exception MutArgument

let () =
  Printexc.register_printer (function
    | MutArgument -> Some (Printf.sprintf "argument specified as mut")
    | _ -> None)

let rec args_names : Parse.prod_field list -> _ = function
  | [] -> []
  | Parse.Decl { kind; name_or_count = Name name; _ } :: fields ->
      let () =
        match kind with Some Parse.Mut -> raise MutArgument | _ -> ()
      in
      name :: args_names fields
  | Decl { name_or_count = Count _; _ } :: _ -> raise NumAsArgumentName
  | Value _ :: _ -> raise ValueAsArgument

exception InvalidBinopOperands of value * value
exception InvalidUnaryOperand of value
exception InvalidIfCond of value
exception UninitializedVal of string
exception UnboundIdent of string

let () =
  Printexc.register_printer (function
    | UnboundIdent name -> Some (Printf.sprintf "unbound ident: \"%s\"" name)
    | _ -> None)

exception Redeclaration of string
exception ImmutableAssign of string
exception InvalidAccessee of value
exception InvalidAccessor of Parse.expr
exception InvalidField of string
exception InvalidCallArgs of string list * prod
exception InvalidCallee of value
exception UnexpectedCtrl

let bool_type_disc_false = 0
let bool_type_disc_true = 1

let bool_type : sum_type =
  [
    { name = "false"; disc = bool_type_disc_false; field_type = None };
    { name = "true"; disc = bool_type_disc_true; field_type = None };
  ]

let bool_from_bool b =
  SumVariant
    {
      type' = bool_type;
      disc = (if b then bool_type_disc_true else bool_type_disc_false);
      field = None;
    }

let is_bool { type'; _ } = type' == bool_type
let bool_not { disc; _ } = bool_from_bool (disc = bool_type_disc_false)

exception ProcTypeWithoutReturn
exception Unreachable

let rec exec_expr expr scopes =
  let exec_binop = exec_binop scopes in
  let exec_uop = exec_uop scopes in
  let exec_num_binop = exec_num_binop scopes in
  let exec_bool_binop = exec_bool_binop scopes in
  let rec eq = function
    | SumVariant v1, SumVariant v2 -> begin
        v1.type' == v2.type' && v1.disc = v2.disc
        &&
        match (v1.field, v2.field) with
        | Some f1, Some f2 -> eq (f1, f2)
        | None, None -> true
        | _ -> raise Unreachable
      end
    | Num n1, Num n2 -> n1 = n2
    | Rune r1, Rune r2 -> r1 = r2
    | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs))
  in
  match expr with
  | Parse.Lit lit -> begin
      match lit with
      | Num n -> return (Num n)
      | Rune r -> return (Rune r)
      | String _s -> raise TODO
    end
  | Id i ->
      let entry_opt = List.find_map (( ! ) >> StringMap.find_opt i) scopes in
      let entry = get_or_else entry_opt @@ fun () -> raise (UnboundIdent i) in
      return (value_of_scope_entry i entry)
  | Uop (uop, operand) -> begin
      match uop with
      | Not ->
          exec_uop operand (function
            | SumVariant variant when is_bool variant ->
                return (bool_not variant)
            | invalid -> raise (InvalidUnaryOperand invalid))
      | UnaryMins ->
          exec_uop operand (function
            | Num n -> return (Num (-n))
            | invalid -> raise (InvalidUnaryOperand invalid))
    end
  | Binop (lhs, binop, rhs) -> begin
      match binop with
      | Plus -> exec_num_binop lhs rhs ( + )
      | Mins -> exec_num_binop lhs rhs ( - )
      | Astr -> exec_num_binop lhs rhs ( * )
      | Slsh -> exec_num_binop lhs rhs ( / )
      | Perc -> exec_num_binop lhs rhs ( mod )
      | And -> exec_bool_binop lhs rhs ( && )
      | Or -> exec_bool_binop lhs rhs ( || )
      | Eq -> exec_binop lhs rhs (eq >> bool_from_bool)
      | Ne -> exec_binop lhs rhs (eq >> not >> bool_from_bool)
      | Le ->
          exec_binop lhs rhs (fun (lhs, rhs) ->
              match (lhs, rhs) with
              | Num n1, Num n2 -> bool_from_bool (n1 <= n2)
              | Rune r1, Rune r2 -> bool_from_bool (r1 <= r2)
              | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs)))
      | Lt ->
          exec_binop lhs rhs (fun (lhs, rhs) ->
              match (lhs, rhs) with
              | Num n1, Num n2 -> bool_from_bool (n1 < n2)
              | Rune r1, Rune r2 -> bool_from_bool (r1 < r2)
              | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs)))
      | Dot -> (
          let accessor =
            match rhs with Id i -> i | _ -> raise (InvalidAccessor rhs)
          in
          let* ctrl = exec_expr lhs scopes in
          match ctrl with
          | Prod fields -> begin
              match
                List.find_opt (fun { name; _ } -> name = Some accessor) fields
              with
              | Some { entry; _ } ->
                  return (value_of_scope_entry accessor entry)
              | None -> raise (InvalidField accessor)
            end
          | Type (Sum type') -> (
              match
                List.find_opt
                  (fun ({ name; _ } : sum_variant_type) -> name = accessor)
                  type'
              with
              | Some { disc; field_type = None; _ } ->
                  return (SumVariant { type'; disc; field = None })
              | Some { disc; field_type = Some _; _ } ->
                  return
                    (Proc
                       (fun fields ->
                         match fields with
                         | [ { name = None | Some "value"; entry } ] ->
                             let value = value_of_scope_entry "value" entry in
                             SumVariant { type'; disc; field = Some value }
                         | _ -> raise (InvalidCallArgs ([ "value" ], fields))))
              | None -> raise (InvalidField accessor))
          | invalid -> raise (InvalidAccessee invalid))
    end
  | If { cond; if_branch; else_branch } -> begin
      let* ctrl = exec_expr cond scopes in
      match ctrl with
      | SumVariant variant
        when is_bool variant && variant.disc = bool_type_disc_true ->
          exec_expr if_branch scopes
      | SumVariant variant
        when is_bool variant && variant.disc = bool_type_disc_false -> begin
          match else_branch with
          | Some else_branch -> exec_expr else_branch scopes
          | None -> return unit_val
        end
      | cond -> raise (InvalidIfCond cond)
    end
  | Sum variants -> exec_sum variants scopes
  | Prod fields ->
      let* fields = exec_prod fields scopes in
      return (Prod fields)
  | Block stmts -> exec_block scopes stmts
  | Proc { type' = { args; _ }; body } ->
      let expected = args_names args in
      return
        (Proc
           (fun fields ->
             let field_pairs =
               try List.combine expected fields
               with Invalid_argument _ ->
                 raise (InvalidCallArgs (expected, fields))
             in
             let fields_scope =
               List.fold_left
                 (fun scope (expected_name, { name; entry; _ }) ->
                   let () =
                     match name with
                     | Some name when name <> expected_name ->
                         raise (InvalidCallArgs (expected, fields))
                     | _ -> ()
                   in
                   StringMap.add expected_name entry scope)
                 StringMap.empty field_pairs
             in
             let ctrl = exec_block (ref fields_scope :: scopes) body in
             match ctrl with
             | None value -> value
             | Brk | Ctn -> raise UnexpectedCtrl
             | Ret value -> Option.value value ~default:unit_val))
  | ProcT { args; return_type = Some return_type } ->
      let* arg_types = exec_arg_types args scopes in
      let* return_type_val = exec_expr return_type scopes in
      let return_type = expect_type return_type_val in
      return (Type (Proc { arg_types; return_type }))
  | ProcT { return_type = None; _ } -> raise ProcTypeWithoutReturn
  | Call { callee; args } -> begin
      let* callee = exec_expr callee scopes in
      match callee with
      | Proc f ->
          let* args = exec_prod args scopes in
          return (f args)
      | invalid -> raise (InvalidCallee invalid)
    end

and exec_binop scopes lhs rhs op =
  let* lhs = exec_expr lhs scopes in
  let* rhs = exec_expr rhs scopes in
  return (op (lhs, rhs))

and exec_num_binop scopes lhs rhs op =
  exec_binop scopes lhs rhs @@ function
  | Num n1, Num n2 -> Num (op n1 n2)
  | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs))

and exec_bool_binop scopes lhs rhs op =
  exec_binop scopes lhs rhs @@ function
  | SumVariant v1, SumVariant v2 when is_bool v1 && is_bool v2 ->
      let d1 = v1.disc <> 0 in
      let d2 = v2.disc <> 0 in
      bool_from_bool (op d1 d2)
  | lhs, rhs -> raise (InvalidBinopOperands (lhs, rhs))

and exec_uop scopes operand op = exec_expr operand scopes >>= op

and exec_sum variants scopes =
  List.fold_left
    (fun ctrl ({ name; value } : Parse.sum_var) ->
      let* variants = ctrl in
      let disc = Oo.id (object end) in
      match value with
      | Some value ->
          let* field_type = exec_expr value scopes in
          let field_type = Some (expect_type field_type) in
          return (variants @ [ { name; disc; field_type } ])
      | None -> return (variants @ [ { name; disc; field_type = None } ]))
    (return []) variants
  >>= fun variants -> return (Type (Sum variants))

and exec_prod fields scopes =
  List.fold_left
    (fun (prev_kind, ctrl) (field : Parse.prod_field) ->
      match ctrl with
      | None fields -> begin
          match field with
          | Parse.Decl
              { kind; name_or_count = Name name; value = Some value; _ } ->
            begin
              let kind = Option.value kind ~default:prev_kind in
              let ctrl = exec_expr value scopes in
              let () =
                match
                  List.find_opt (( = ) name)
                    (List.filter_map (fun { name; _ } -> name) fields)
                with
                | Some name -> raise (Redeclaration name)
                | None -> ()
              in
              match ctrl with
              | None value ->
                  let name = Some name in
                  let entry = scope_entry value kind in
                  (kind, return (fields @ [ { name; entry } ]))
              | Brk -> (kind, Brk)
              | Ctn -> (kind, Ctn)
              | Ret value -> (kind, Ret value)
            end
          | Value value -> (
              let ctrl = exec_expr value scopes in
              match ctrl with
              | None value ->
                  let name = Option.None in
                  let entry = scope_entry value prev_kind in
                  (prev_kind, return (fields @ [ { name; entry } ]))
              | Brk -> (prev_kind, Brk)
              | Ctn -> (prev_kind, Ctn)
              | Ret value -> (prev_kind, Ret value))
          | _ -> raise TODO
        end
      | Brk -> (prev_kind, Brk)
      | Ctn -> (prev_kind, Ctn)
      | Ret value -> (prev_kind, Ret value))
    (Parse.Val, return [])
    fields
  |> snd

and exec_arg_types args scopes =
  List.fold_left
    (fun (prev_kind, ctrl) (arg : Parse.prod_field) ->
      match ctrl with
      | None args -> begin
          match arg with
          | Parse.Decl
              {
                kind;
                name_or_count = Name name;
                type' = Some type';
                value = None;
              } -> (
              let kind = Option.value kind ~default:prev_kind in
              let ctrl = exec_expr type' scopes in
              let () =
                match
                  List.find_opt
                    (fun ({ name = existing_name; _ } : prod_field_type) ->
                      existing_name = name)
                    args
                with
                | Some { name; _ } -> raise (Redeclaration name)
                | None -> ()
              in
              match ctrl with
              | None type_val ->
                  let type' = expect_type type_val in
                  (kind, return (args @ [ { kind; name; type' } ]))
              | Brk -> (kind, Brk)
              | Ctn -> (kind, Ctn)
              | Ret value -> (kind, Ret value))
          | _ -> raise TODO
        end
      | Brk -> (prev_kind, Brk)
      | Ctn -> (prev_kind, Ctn)
      | Ret value -> (prev_kind, Ret value))
    (Parse.Val, return [])
    args
  |> snd

and exec_block scopes = function
  | [ Expr expr ] -> exec_expr expr (ref StringMap.empty :: scopes)
  | [ stmt ] ->
      let* _ = exec_stmt stmt (ref StringMap.empty :: scopes) in
      return unit_val
  | stmts ->
      let* _ = exec_nonsingle_block stmts (ref StringMap.empty :: scopes) in
      return unit_val

and exec_nonsingle_block stmts scopes =
  match stmts with
  | stmt :: stmts ->
      let* _ = exec_stmt stmt scopes in
      exec_nonsingle_block stmts scopes
  | [] -> return ()

(* scopes must be non-empty. *)
and exec_stmt stmt scopes =
  match stmt with
  | Parse.Brk -> Brk
  | Ctn -> Ctn
  | Ret value -> begin
      match value with
      | Some value ->
          let* value = exec_expr value scopes in
          Ret (Some value)
      | None -> Ret None
    end
  | Decl { kind; name; value; _ } -> begin
      match (kind, value) with
      | _, Some value ->
          let* value = exec_expr value scopes in
          let entry = scope_entry value kind in
          let scope = List.hd scopes in
          let () =
            match StringMap.find_opt name !scope with
            | Some _ -> raise (Redeclaration name)
            | None -> ()
          in
          scope := StringMap.add name entry !scope;
          return ()
      | Mut, None ->
          let scope = List.hd scopes in
          let () =
            match StringMap.find_opt name !scope with
            | Some _ -> raise (Redeclaration name)
            | None -> ()
          in
          scope := StringMap.add name (Mut (ref Option.None)) !scope;
          return ()
      | Val, None -> raise (UninitializedVal name)
    end
  | Assign { assignee; value } -> begin
      let try_scope_entry_assign name assignee' scopes =
        match assignee' with
        | Mut value_ref ->
            let* value = exec_expr value scopes in
            value_ref := Some value;
            return ()
        | _ -> raise (ImmutableAssign name)
      in
      match assignee with
      | Id i -> begin
          match
            List.find_map (fun scope -> StringMap.find_opt i !scope) scopes
          with
          | Some assignee -> try_scope_entry_assign i assignee scopes
          | None -> raise (UnboundIdent i)
        end
      | Binop (accessee, Dot, Id accessor) -> begin
          let* accessee = exec_expr accessee scopes in
          match accessee with
          | Prod fields -> begin
              match
                List.find_opt (fun { name; _ } -> name = Some accessor) fields
              with
              | Some { entry; _ } ->
                  try_scope_entry_assign accessor entry scopes
              | None -> raise (InvalidField accessor)
            end
          | invalid -> raise (InvalidAccessee invalid)
        end
      | _ -> raise TODO
    end
  | Loop body -> exec_loop body scopes
  | Expr expr ->
      let* _ = exec_expr expr scopes in
      return ()

and exec_loop body scopes =
  match exec_expr body scopes with
  | Brk -> return ()
  | Ret value -> Ret value
  | _ -> exec_loop body scopes

let rec stringify value =
  let indent text = String.split_on_char '\n' text |> String.concat "\n  " in
  match value with
  | Num n -> string_of_int n
  | Rune r -> "'" ^ Char.escaped r ^ "'"
  | SumVariant { type'; disc; field } ->
      let name =
        match
          List.find_opt
            (fun ({ disc = disc'; _ } : sum_variant_type) -> disc' = disc)
            type'
        with
        | None -> raise Unreachable
        | Some { name; _ } -> name
      in
      let field_string =
        Option.map (fun field -> "(" ^ (stringify field |> indent) ^ ")") field
      in
      name ^ Option.value field_string ~default:""
  | Prod [] -> "()"
  | Prod fields ->
      let field_strings =
        List.mapi
          (fun i { name; entry } ->
            let name_string = Option.value name ~default:(string_of_int i) in
            let entry_string =
              match entry with
              | Mut value_ref -> begin
                  match !value_ref with
                  | Some value -> stringify value |> indent
                  | None -> "(uninitialized)"
                end
              | Val value -> stringify value |> indent
            in
            name_string ^ " = " ^ entry_string ^ ",")
          fields
      in
      let fields_string = String.concat "\n  " field_strings in
      "(\n  " ^ fields_string ^ "\n)"
  | Proc _ -> "proc(...) { ... }"
  | Type t -> begin
      match t with
      | Num -> "num"
      | Rune -> "rune"
      | Sum [] -> "[]"
      | Sum variants ->
          let variant_strings =
            List.map
              (fun { name; field_type; _ } ->
                let field_type_string =
                  Option.map
                    (fun field_type ->
                      "(" ^ (stringify (Type field_type) |> indent) ^ ")")
                    field_type
                in
                name ^ Option.value field_type_string ~default:"" ^ ",")
              variants
          in
          let variants_string = String.concat "\n  " variant_strings in
          "[\n  " ^ variants_string ^ "\n]"
      | Prod [] -> "()"
      | Prod fields ->
          let field_strings =
            List.map
              (fun { kind; name; type' } ->
                let kind_string =
                  match kind with Mut -> "mut" | Val -> "val"
                in
                let type_string = stringify (Type type') in
                kind_string ^ " " ^ name ^ ": " ^ type_string)
              fields
          in
          let fields_string = String.concat "\n  " field_strings in
          "(\n  " ^ fields_string ^ "\n)"
      | Proc { arg_types; return_type } ->
          let arg_types_string =
            match arg_types with
            | [] -> "()"
            | _ ->
                let arg_type_strings =
                  List.map
                    (fun { kind; name; type' } ->
                      let kind_string =
                        match kind with Parse.Mut -> "mut" | Val -> "val"
                      in
                      let type_string = stringify (Type type') in
                      kind_string ^ " " ^ name ^ ": " ^ type_string ^ ",")
                    arg_types
                in
                "(\n  " ^ String.concat "\n  " arg_type_strings ^ "\n)"
          in
          let return_type_string = stringify (Type return_type) in
          "proc" ^ arg_types_string ^ ": " ^ return_type_string
    end

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
  [%expect "true"]

let%expect_test _ =
  stringify
    (SumVariant
       {
         type' =
           [
             { name = "Bar"; disc = 0; field_type = None };
             { name = "Baz"; disc = 9; field_type = Some Rune };
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
  stringify (Prod [ { name = Some "foo"; entry = Val (Num 9) } ])
  |> print_endline;
  [%expect {|
(
  foo = 9,
)
|}]

let%expect_test _ =
  stringify
    (Prod
       [
         { name = Some "foo"; entry = Val (Num 9) };
         { name = Some "bar"; entry = Mut (ref (Some (Rune 'r'))) };
         { name = Some "baz"; entry = Mut (ref Option.None) };
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
           name = Some "foo";
           entry =
             Val
               (Prod
                  [
                    {
                      name = Some "bar";
                      entry =
                        Val
                          (Prod [ { name = Some "baz"; entry = Val (Prod []) } ]);
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
  stringify (Proc (fun _ -> unit_val)) |> print_endline;
  [%expect "proc(...) { ... }"]

let%expect_test _ =
  stringify (Type Num) |> print_endline;
  [%expect "num"]

let%expect_test _ =
  stringify (Type Rune) |> print_endline;
  [%expect "rune"]

let%expect_test _ =
  stringify (Type (Sum [])) |> print_endline;
  [%expect "[]"]

let%expect_test _ =
  stringify (Type (Sum [ { name = "Foo"; disc = 0; field_type = None } ]))
  |> print_endline;
  [%expect {|
[
  Foo,
]
|}]

let%expect_test _ =
  stringify (Type (Sum [ { name = "Foo"; disc = 0; field_type = Some Rune } ]))
  |> print_endline;
  [%expect {|
[
  Foo(rune),
]
|}]

let%expect_test _ =
  stringify
    (Type
       (Sum
          [
            { name = "Foo"; disc = 0; field_type = Some Rune };
            { name = "Bar"; disc = 1; field_type = None };
            { name = "Baz"; disc = 2; field_type = Some Num };
          ]))
  |> print_endline;
  [%expect {|
[
  Foo(rune),
  Bar,
  Baz(num),
]
|}]

let%expect_test _ =
  stringify (Type (Proc { arg_types = []; return_type = Rune }))
  |> print_endline;
  [%expect "proc(): rune"]

let%expect_test _ =
  stringify
    (Type
       (Proc
          {
            arg_types = [ { kind = Parse.Val; name = "foo"; type' = Num } ];
            return_type = Sum [];
          }))
  |> print_endline;
  [%expect {|
  proc(
    val foo: num,
  ): []
|}]

let%expect_test _ =
  stringify
    (Type
       (Proc
          {
            arg_types =
              [
                { kind = Parse.Val; name = "foo"; type' = Num };
                { kind = Mut; name = "bar"; type' = Rune };
              ];
            return_type = Sum [];
          }))
  |> print_endline;
  [%expect {|
  proc(
    val foo: num,
    mut bar: rune,
  ): []
|}]

let intrinsics =
  [
    {
      name = Some "bsPrintln";
      entry =
        Val
          (Proc
             (fun fields ->
               match fields with
               | [ { name = None | Some "value"; entry } ] ->
                   let value = value_of_scope_entry "value" entry in
                   let () = stringify value |> print_endline in
                   unit_val
               | _ -> raise (InvalidCallArgs ([ "value" ], fields))));
    };
  ]

let builtins =
  let builtins = StringMap.empty in
  let builtins = StringMap.add "false" (Val (bool_from_bool false)) builtins in
  let builtins = StringMap.add "true" (Val (bool_from_bool true)) builtins in
  let builtins = StringMap.add "num" (Val (Type Num)) builtins in
  let builtins = StringMap.add "rune" (Val (Type Rune)) builtins in
  StringMap.add "intrinsics" (Val (Prod intrinsics)) builtins

let exec_ast ast =
  let ctrl = exec_expr ast [ ref builtins ] in
  match ctrl with
  | None value -> value
  | Brk | Ctn | Ret _ -> raise UnexpectedCtrl

exception ExpectedProc

let exec path =
  let text = Core.In_channel.read_lines path |> String.concat "\n" in
  let ast = Parse.parse text in
  let _ = match exec_ast ast with Proc f -> f [] | _ -> raise ExpectedProc in
  ()

let assert_raises = OUnit2.assert_raises
let parse = Parse.parse

let%test _ =
  let ast = parse "5 + 9" in
  Num 14 = exec_ast ast

let%test_unit _ =
  let ast = parse "5 == true" in
  let f () = exec_ast ast in
  assert_raises (InvalidBinopOperands (Num 5, bool_from_bool true)) f

let%test_unit _ =
  let ast = parse "false + true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (bool_from_bool false, bool_from_bool true))
    f

let%test _ =
  let ast = parse "5 - 9" in
  Num (-4) = exec_ast ast

let%test_unit _ =
  let ast = parse "false - true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (bool_from_bool false, bool_from_bool true))
    f

let%test _ =
  let ast = parse "5 * 9" in
  Num 45 = exec_ast ast

let%test_unit _ =
  let ast = parse "false * true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (bool_from_bool false, bool_from_bool true))
    f

let%test _ =
  let ast = parse "5 / 9" in
  Num 0 = exec_ast ast

let%test_unit _ =
  let ast = parse "false / true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (bool_from_bool false, bool_from_bool true))
    f

let%test _ =
  let ast = parse "5 % 9" in
  Num 5 = exec_ast ast

let%test_unit _ =
  let ast = parse "false % true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (bool_from_bool false, bool_from_bool true))
    f

let%test _ =
  let ast = parse "true && false" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "true && true" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "5 && 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidBinopOperands (Num 5, Num 9)) f

let%test _ =
  let ast = parse "false || true" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "true || false" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "false || false" in
  bool_from_bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "5 || 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidBinopOperands (Num 5, Num 9)) f

let%test _ =
  let ast = parse "!false" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "!true" in
  bool_from_bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "!5" in
  let f () = exec_ast ast in
  assert_raises (InvalidUnaryOperand (Num 5)) f

let%test _ =
  let ast = parse "-5" in
  Num (-5) = exec_ast ast

let%test_unit _ =
  let ast = parse "-false" in
  let f () = exec_ast ast in
  assert_raises (InvalidUnaryOperand (bool_from_bool false)) f

let%test _ =
  let ast = parse "false == true" in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast = parse "true == true" in
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
  let ast = parse "false != true" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "true != true" in
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
  let ast = parse "false <= true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (bool_from_bool false, bool_from_bool true))
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
  let ast = parse "false < true" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidBinopOperands (bool_from_bool false, bool_from_bool true))
    f

let%test _ =
  let ast = parse "if true then 5 else 9" in
  Num 5 = exec_ast ast

let%test _ =
  let ast = parse "if false then 5 else 9" in
  Num 9 = exec_ast ast

let%test _ =
  let ast = parse "if false then 5" in
  unit_val = exec_ast ast

let%test_unit _ =
  let ast = parse "if 9 then 5 else 9" in
  let f () = exec_ast ast in
  assert_raises (InvalidIfCond (Num 9)) f

let%test _ =
  let ast = parse "()" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9)" in
  Prod [ { name = Some "i"; entry = Val (Num 9) } ] = exec_ast ast

let%test_unit _ =
  let ast = parse "(val i = 9, val i = 9)" in
  let f () = exec_ast ast in
  assert_raises (Redeclaration "i") f

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = true)" in
  Prod
    [
      { name = Some "i"; entry = Val (Num 9) };
      { name = Some "j"; entry = Val (Rune 'a') };
      { name = Some "k"; entry = Mut (ref (Some (bool_from_bool true))) };
    ]
  = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9).i" in
  Num 9 = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = true).j" in
  Rune 'a' = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = true).k" in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast = parse "(val i = 9, val j = 'a', mut k = true).k" in
  bool_from_bool true = exec_ast ast

let%test_unit _ =
  let ast = parse "().i" in
  let f () = exec_ast ast in
  assert_raises (InvalidField "i") f

let%test_unit _ =
  let ast = parse "1.i" in
  let f () = exec_ast ast in
  assert_raises (InvalidAccessee (Num 1)) f

let%test _ =
  let ast = parse "[]" in
  match exec_ast ast with Type (Sum []) -> true | _ -> false

let%test _ =
  let ast = parse "[Red, Green(num), Blue(rune)]" in
  match exec_ast ast with
  | Type
      (Sum
        [
          { name = "Red"; field_type = None; _ };
          { name = "Green"; field_type = Some Num; _ };
          { name = "Blue"; field_type = Some Rune; _ };
        ]) ->
      true
  | _ -> false

let%test _ =
  let ast = parse "[Red].Red" in
  match exec_ast ast with SumVariant { field = None; _ } -> true | _ -> false

let%test _ =
  let ast = parse "[Green(num)].Green(value = 5)" in
  match exec_ast ast with
  | SumVariant { field = Some (Num 5); _ } -> true
  | _ -> false

let%test_unit _ =
  let ast = parse "[Green(num)].Green(foo = 5)" in
  let f () = exec_ast ast in
  assert_raises
    (InvalidCallArgs
       ([ "value" ], [ { name = Some "foo"; entry = Val (Num 5) } ]))
    f

let%test_unit _ =
  let ast = parse "[].Blue" in
  let f () = exec_ast ast in
  assert_raises (InvalidField "Blue") f

let%test _ =
  (*
  The two sums are separate, so the variants aren't equal though they happen to
  have the same names
  *)
  let ast = parse "[Red].Red == [Red].Red" in
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
  in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    proc() {
      val sum = [Red, Green(num), Blue]
      ret sum.Green(value = 5) == sum.Green(value = 5)
    }()
  |}
  in
  bool_from_bool true = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    proc() {
      val sum = [Red, Green(num), Blue]
      ret sum.Green(value = 5) == sum.Green(value = 9)
    }()
  |}
  in
  bool_from_bool false = exec_ast ast

let%test _ =
  let ast =
    parse
      {|
    proc() {
      val sum = [Red, Green(num), Blue(num)]
      ret sum.Green(value = 5) == sum.Blue(value = 5)
    }()
  |}
  in
  bool_from_bool false = exec_ast ast

let%test_unit _ =
  let ast = parse "[].Blue" in
  let f () = exec_ast ast in
  assert_raises (InvalidField "Blue") f

let%test_unit _ =
  let ast = parse "[Blue(5)]" in
  let f () = exec_ast ast in
  assert_raises (ValueAsType (Num 5)) f

let%test _ =
  let ast = parse "{ proc() { } }()" in
  unit_val = exec_ast ast

let%test _ =
  let ast = parse "{ proc(val i: Nat) { i + 1 } }(2)" in
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
    (InvalidCallArgs ([ "i" ], [ { name = Some "j"; entry = Val (Num 2) } ]))
    f

let%test_unit _ =
  let ast = parse "{ proc(val i: Nat) { i } }()" in
  let f () = exec_ast ast in
  assert_raises (InvalidCallArgs ([ "i" ], [])) f

let%test_unit _ =
  let ast = parse "proc(mut i: Nat) { i }" in
  let f () = exec_ast ast in
  assert_raises MutArgument f

let%test_unit _ =
  let ast = parse "proc(val 5: Nat) { }" in
  let f () = exec_ast ast in
  assert_raises NumAsArgumentName f

let%test_unit _ =
  let ast = parse "proc('a') { }" in
  let f () = exec_ast ast in
  assert_raises ValueAsArgument f

let%test_unit _ =
  let ast = parse "{ proc() { foo } }()" in
  let f () = exec_ast ast in
  assert_raises (UnboundIdent "foo") f

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
  assert_raises (UseBeforeInitialization "i") f

let%test _ =
  let ast =
    parse
      {|
    {
      proc() {
        mut b = false
        loop {
          if b then {
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
        if { if true then { ret 9 } else true } then {
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
  assert_raises UnexpectedCtrl f

let%test_unit _ =
  let ast = parse "{ proc() { ctn } }()" in
  let f () = exec_ast ast in
  assert_raises UnexpectedCtrl f

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
  assert_raises (InvalidCallee (Num 1)) f

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
  assert_raises (Redeclaration "i") f

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
  assert_raises (Redeclaration "i") f

let%test_unit _ =
  let ast = parse "{ proc() { val i } }()" in
  let f () = exec_ast ast in
  assert_raises (UninitializedVal "i") f

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
  assert_raises (ImmutableAssign "i") f

let%test_unit _ =
  let ast = parse {|
    {
      proc() {
        i = 1
      }
    }()
  |} in
  let f () = exec_ast ast in
  assert_raises (UnboundIdent "i") f

let%test_unit _ =
  let ast = parse "{ brk }" in
  let f () = exec_ast ast in
  assert_raises UnexpectedCtrl f

let%test_unit _ =
  let ast = parse "{ ctn }" in
  let f () = exec_ast ast in
  assert_raises UnexpectedCtrl f

let%test_unit _ =
  let ast = parse "{ ret }" in
  let f () = exec_ast ast in
  assert_raises UnexpectedCtrl f

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
  assert_raises (InvalidField "bogus") f

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
  assert_raises (InvalidAccessee (Num 1)) f

let%test _ =
  let ast = parse "proc(): num" in
  Type (Proc { arg_types = []; return_type = Num }) = exec_ast ast

let%test _ =
  let ast = parse "proc(foo: num): num" in
  Type
    (Proc
       {
         arg_types = [ { kind = Parse.Val; name = "foo"; type' = Num } ];
         return_type = Num;
       })
  = exec_ast ast

let%test _ =
  let ast = parse "proc(mut foo: num, baz: rune): num" in
  Type
    (Proc
       {
         arg_types =
           [
             { kind = Parse.Mut; name = "foo"; type' = Num };
             { kind = Mut; name = "baz"; type' = Rune };
           ];
         return_type = Num;
       })
  = exec_ast ast

let%test_unit _ =
  let ast = parse "proc(i: num, i: num): num" in
  let f () = exec_ast ast in
  assert_raises (Redeclaration "i") f

let%test_unit _ =
  let ast = parse "proc(i: num)" in
  let f () = exec_ast ast in
  assert_raises ProcTypeWithoutReturn f
