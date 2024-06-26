open Util

type pos = StringPos of Starpath.string_pos | FilePos of Starpath.file_pos

let string_of_pos = function
  | StringPos pos -> Starpath.StringPos.string_of_pos pos
  | FilePos pos -> Starpath.FilePos.string_of_pos pos

exception TODO

module StringMap = Map.Make (String)

type value =
  | Num of int
  | Rune of char
  | SumVariant of sum_variant
  | Prod of prod
  | Proc of (pos -> prod -> value)
  | Ref of ref'
  | Type of type'

and prod_entry = Mut of value option ref | Val of value
and prod_field = { name : string option; entry : prod_entry }
and prod = prod_field list
and sum_variant = { type' : sum_type; disc : int; field : value option }
and ref_value = Singleton of value ref | Array of value list ref
and ref' = { kind : Parse.kind; value : ref_value }

and type' =
  | Num
  | Rune
  | Sum of sum_type
  | Prod of prod_field_type list
  | Proc of proc_type
  | Ref of type'

and sum_type = sum_variant_type list
and sum_variant_type = { name : string; disc : int; field_type : type' option }
and prod_field_type = { kind : Parse.kind; name : string; type' : type' }
and proc_type = { arg_types : prod_field_type list; return_type : type' }

exception ValueAsType of pos * value

let () =
  Printexc.register_printer @@ function
  | ValueAsType (pos, _) ->
      Some (Printf.sprintf "%s: value used as type" (string_of_pos pos))
  | _ -> None

let expect_type pos = function
  | Type t -> t
  | invalid -> raise (ValueAsType (pos, invalid))

let unit_val = Prod []

type 'a ctrl =
  | Brk of pos
  | Ctn of pos
  | Ret of pos * value option
  | None of 'a

let return a = None a

let ( >>= ) ctrl f =
  match ctrl with
  | Brk pos -> Brk pos
  | Ctn pos -> Ctn pos
  | Ret (pos, value) -> Ret (pos, value)
  | None a -> f a

let ( <$> ) : 'a 'b. _ = fun f ctrl -> ctrl >>= (f >> return)
let ( let* ) = ( >>= )
let ( let+ ) : 'a 'b. _ = fun ctrl f -> f <$> ctrl

let rec fold_left_ctrl f init = function
  | [] -> return init
  | x :: xs ->
      let* y = f init x in
      fold_left_ctrl f y xs

let rec map_ctrl f = function
  | [] -> return []
  | x :: xs ->
      let* y = f x in
      let+ ys = map_ctrl f xs in
      y :: ys

let rec try_fold_left_ctrl f init : _ -> _ option = function
  | [] -> Some (return init)
  | x :: xs -> begin
      Option.bind (f init x) @@ function
      | Brk pos -> Some (Brk pos)
      | Ctn pos -> Some (Ctn pos)
      | Ret (pos, value) -> Some (Ret (pos, value))
      | None y -> try_fold_left_ctrl f y xs
    end

let rec map_ctrl f = function
  | [] -> return []
  | x :: xs ->
      let* y = f x in
      let+ ys = map_ctrl f xs in
      y :: ys

type scope_entry =
  | Mut of value option ref
  | Val of value
  | Dyn of value ctrl Lazy.t

let scope_entry value = function
  | Parse.Mut -> Mut (ref (Some value))
  | Val -> Val value

let prod_entry value : _ -> prod_entry = function
  | Parse.Mut -> Mut (ref (Some value))
  | Val -> Val value

let scope_entry_of_prod_entry : prod_entry -> _ = function
  | Mut value_ref -> Mut value_ref
  | Val value -> Val value

exception UseBeforeInitialization of pos * string

let () =
  Printexc.register_printer @@ function
  | UseBeforeInitialization (pos, name) ->
      Some
        (Printf.sprintf "%s: use of \"%s\" before initialization"
           (string_of_pos pos) name)
  | _ -> None

let value_of_prod_entry pos name : prod_entry -> _ = function
  | Mut value_ref ->
      get_or_else !value_ref (fun () ->
          raise (UseBeforeInitialization (pos, name)))
  | Val value -> value

let value_of_scope_entry pos name = function
  | Mut value_ref ->
      return
        (get_or_else !value_ref (fun () ->
             raise (UseBeforeInitialization (pos, name))))
  | Val value -> return value
  | Dyn value_fun -> Lazy.force value_fun

exception NumAsArgumentName of pos

let () =
  Printexc.register_printer @@ function
  | NumAsArgumentName pos ->
      Some
        (Printf.sprintf "%s: number specified as argument name"
           (string_of_pos pos))
  | _ -> None

exception ValueAsArgument of pos

let () =
  Printexc.register_printer @@ function
  | ValueAsArgument pos ->
      Some
        (Printf.sprintf "%s:value specified in function declaration"
           (string_of_pos pos))
  | _ -> None

exception MutArgument of pos

let () =
  Printexc.register_printer @@ function
  | MutArgument pos ->
      Some (Printf.sprintf "%s: argument specified as mut" (string_of_pos pos))
  | _ -> None

let rec args_names : _ Parse.prod_field list -> _ = function
  | [] -> []
  | Parse.Decl { kind; name_or_count = _, Name name; _ } :: fields ->
      let () =
        match kind with
        | Some (pos, Parse.Mut) -> raise (MutArgument pos)
        | _ -> ()
      in
      name :: args_names fields
  | Decl { name_or_count = count_pos, Count _; _ } :: _ ->
      raise (NumAsArgumentName count_pos)
  | Value (pos, _) :: _ -> raise (ValueAsArgument pos)

exception InvalidBinopOperands of pos * value * value
exception InvalidUnaryOperand of pos * value
exception InvalidIfCond of pos * value
exception UninitializedVal of pos * string

let () =
  Printexc.register_printer @@ function
  | UninitializedVal (pos, name) ->
      Some
        (Printf.sprintf "%s: uninitialized value: \"%s\"" (string_of_pos pos)
           name)
  | _ -> None

exception UnboundIdent of pos * string

let () =
  Printexc.register_printer @@ function
  | UnboundIdent (pos, name) ->
      Some (Printf.sprintf "%s: unbound ident: \"%s\"" (string_of_pos pos) name)
  | _ -> None

exception Redeclaration of pos * string

let () =
  Printexc.register_printer @@ function
  | Redeclaration (pos, name) ->
      Some
        (Printf.sprintf "%s: redeclaration of: \"%s\"" (string_of_pos pos) name)
  | _ -> None

exception ImmutableAssign of pos * string
exception InvalidAccessee of pos * value
exception InvalidAccessor of pos
exception InvalidField of pos * string
exception InvalidCallArgs of pos * string list * prod

let () =
  Printexc.register_printer @@ function
  | InvalidCallArgs (pos, _, _) ->
      Some (Printf.sprintf "%s: invalid call args" (string_of_pos pos))
  | _ -> None

exception InvalidCallee of pos * value
exception UnexpectedCtrl of pos

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

exception ProcTypeWithoutReturn of pos
exception Unreachable

let ref_array_of_string s =
  let cs = List.init (String.length s) (String.get s) in
  Ref { kind = Parse.Val; value = Array (ref (List.map (fun x -> Rune x) cs)) }

let string_of_char_ref_array cs =
  Option.map
    (List.to_seq >> String.of_seq)
    (try_map (function Rune r -> Some r | _ -> None) cs)

let rec copy = function
  | (Num _ | Rune _ | Proc _ | Ref _ | Type _) as x -> x
  | SumVariant ({ field; _ } as variant) ->
      SumVariant { variant with field = Option.map copy field }
  | Prod prod -> Prod (copy_prod prod)

and copy_prod prod =
  let copy_entry : prod_entry -> prod_entry = function
    | Mut value -> Mut (ref (Option.map copy !value))
    | Val value -> Val (copy value)
  in
  let copy_field { name; entry } = { name; entry = copy_entry entry } in
  List.map copy_field prod

let rec deref = function Ref { value = Singleton x; _ } -> deref !x | x -> x

let rec deref_mut = function
  | Ref { kind = Parse.Mut; value = Singleton x } -> deref_mut !x
  | x -> x

exception NeitherValueNorTypeProd of pos

let rec exec_expr expr scopes =
  let exec_binop = exec_binop scopes in
  let exec_uop = exec_uop scopes in
  let exec_num_binop = exec_num_binop scopes in
  let exec_bool_binop = exec_bool_binop scopes in
  match expr with
  | Parse.Lit lit -> begin
      match lit with
      | Num n -> return (Num n)
      | Rune r -> return (Rune r)
      | String s -> return (ref_array_of_string s)
    end
  | Id (pos, i) ->
      let entry_opt = List.find_map (( ! ) >> StringMap.find_opt i) scopes in
      let entry =
        get_or_else entry_opt @@ fun () -> raise (UnboundIdent (pos, i))
      in
      value_of_scope_entry pos i entry
  | Uop (pos, uop, operand) -> begin
      match uop with
      | Not ->
          exec_uop operand (function
            | SumVariant variant when is_bool variant ->
                return (bool_not variant)
            | invalid -> raise (InvalidUnaryOperand (pos, invalid)))
      | UnaryMins ->
          exec_uop operand (function
            | Num n -> return (Num (-n))
            | invalid -> raise (InvalidUnaryOperand (pos, invalid)))
      (* TODO: Handle array refs. *)
      | MutRef ->
          exec_uop operand @@ fun x ->
          return (Ref { kind = Parse.Mut; value = Singleton (ref x) })
      | Ref ->
          exec_uop operand @@ fun x ->
          return (Ref { kind = Parse.Val; value = Singleton (ref x) })
      | Deref ->
          exec_uop operand (function
            | Ref { value = Singleton { contents }; _ } -> return contents
            | Ref { value = Array _; _ } -> raise TODO
            | invalid -> raise (InvalidUnaryOperand (pos, invalid)))
    end
  | Binop (pos, lhs, binop, rhs_pos, rhs) -> begin
      let rec eq = function
        | SumVariant v1, SumVariant v2 -> begin
            v1.type' = v2.type' && v1.disc = v2.disc
            &&
            match (v1.field, v2.field) with
            | Some f1, Some f2 -> eq (f1, f2)
            | None, None -> true
            | _ -> raise Unreachable
          end
        | Num n1, Num n2 -> n1 = n2
        | Rune r1, Rune r2 -> r1 = r2
        | lhs, rhs -> raise (InvalidBinopOperands (pos, lhs, rhs))
      in
      match binop with
      | Plus -> exec_num_binop pos lhs rhs ( + )
      | Mins -> exec_num_binop pos lhs rhs ( - )
      | Astr -> exec_num_binop pos lhs rhs ( * )
      | Slsh -> exec_num_binop pos lhs rhs ( / )
      | Perc -> exec_num_binop pos lhs rhs ( mod )
      | And -> exec_bool_binop pos lhs rhs ( && )
      | Or -> exec_bool_binop pos lhs rhs ( || )
      | Eq -> exec_binop lhs rhs (eq >> bool_from_bool)
      | Ne -> exec_binop lhs rhs (eq >> not >> bool_from_bool)
      | Le ->
          exec_binop lhs rhs (fun (lhs, rhs) ->
              match (lhs, rhs) with
              | Num n1, Num n2 -> bool_from_bool (n1 <= n2)
              | Rune r1, Rune r2 -> bool_from_bool (r1 <= r2)
              | lhs, rhs -> raise (InvalidBinopOperands (pos, lhs, rhs)))
      | Lt ->
          exec_binop lhs rhs (fun (lhs, rhs) ->
              match (lhs, rhs) with
              | Num n1, Num n2 -> bool_from_bool (n1 < n2)
              | Rune r1, Rune r2 -> bool_from_bool (r1 < r2)
              | lhs, rhs -> raise (InvalidBinopOperands (pos, lhs, rhs)))
      | Dot -> begin
          let accessor_pos, accessor =
            match rhs with
            | Id (pos, i) -> (pos, i)
            | _ -> raise (InvalidAccessor rhs_pos)
          in
          let+ ctrl = exec_expr lhs scopes in
          match deref ctrl with
          | Prod fields -> begin
              match
                List.find_opt (fun { name; _ } -> name = Some accessor) fields
              with
              | Some { entry; _ } ->
                  value_of_prod_entry accessor_pos accessor entry
              | None -> raise (InvalidField (accessor_pos, accessor))
            end
          | Type (Sum type') -> (
              match
                List.find_opt
                  (fun ({ name; _ } : sum_variant_type) -> name = accessor)
                  type'
              with
              | Some { disc; field_type = None; _ } ->
                  SumVariant { type'; disc; field = None }
              | Some { disc; field_type = Some _; _ } ->
                  Proc
                    (fun call_pos fields ->
                      match fields with
                      | [ { name = None | Some "value"; entry = Val value } ] ->
                          SumVariant { type'; disc; field = Some value }
                      | _ ->
                          raise
                            (InvalidCallArgs (call_pos, [ "value" ], fields)))
              | None -> raise (InvalidField (accessor_pos, accessor)))
          | invalid -> raise (InvalidAccessee (pos, invalid))
        end
    end
  | If { cond = cond_pos, cond; if_branch; else_branch } -> begin
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
      | cond -> raise (InvalidIfCond (cond_pos, cond))
    end
  | Sum variants -> exec_sum variants scopes
  | Prod (pos, fields) -> begin
      let+ res = exec_prod pos fields scopes in
      match res with
      | Either.Left fields -> Prod fields
      | Right prod_type -> Type prod_type
    end
  | Block stmts -> exec_block scopes stmts
  | Proc { type' = { args = _, { fields; _ }; _ }; body } ->
      let expected = args_names fields in
      return
        (Proc
           (fun call_pos fields ->
             let field_pairs =
               try List.combine expected fields
               with Invalid_argument _ ->
                 raise (InvalidCallArgs (call_pos, expected, fields))
             in
             let fields_scope =
               List.fold_left
                 (fun scope (expected_name, { name; entry; _ }) ->
                   let () =
                     match name with
                     | Some name when name <> expected_name ->
                         raise (InvalidCallArgs (call_pos, expected, fields))
                     | _ -> ()
                   in
                   StringMap.add expected_name entry scope)
                 StringMap.empty field_pairs
             in
             let scope = StringMap.map scope_entry_of_prod_entry fields_scope in
             let ctrl = exec_block (ref scope :: scopes) body in
             match ctrl with
             | None value -> value
             | Brk pos | Ctn pos -> raise (UnexpectedCtrl pos)
             | Ret (_, value) -> Option.value value ~default:unit_val))
  | ProcT
      (_, { args = _, args; return_type = Some (return_type_pos, return_type) })
    ->
      let* arg_types = exec_arg_types args scopes in
      let+ return_type_val = exec_expr return_type scopes in
      let return_type = expect_type return_type_pos return_type_val in
      Type (Proc { arg_types; return_type })
  | ProcT (pos, { return_type = None; _ }) -> raise (ProcTypeWithoutReturn pos)
  | Call (pos, { callee; args }) -> begin
      let* callee = exec_expr callee scopes in
      match callee with
      | Proc f -> begin
          let+ res = exec_prod pos args scopes in
          match res with
          | Either.Left args -> f pos (copy_prod args)
          | Right _ -> raise TODO
        end
      | invalid -> raise (InvalidCallee (pos, invalid))
    end

and exec_binop scopes lhs rhs op =
  let* lhs = exec_expr lhs scopes in
  let+ rhs = exec_expr rhs scopes in
  op (lhs, rhs)

and exec_num_binop scopes pos lhs rhs op =
  exec_binop scopes lhs rhs @@ function
  | Num n1, Num n2 -> Num (op n1 n2)
  | lhs, rhs -> raise (InvalidBinopOperands (pos, lhs, rhs))

and exec_bool_binop scopes pos lhs rhs op =
  exec_binop scopes lhs rhs @@ function
  | SumVariant v1, SumVariant v2 when is_bool v1 && is_bool v2 ->
      let d1 = v1.disc <> 0 in
      let d2 = v2.disc <> 0 in
      bool_from_bool (op d1 d2)
  | lhs, rhs -> raise (InvalidBinopOperands (pos, lhs, rhs))

and exec_uop scopes operand op = exec_expr operand scopes >>= op

and exec_sum variants scopes =
  map_ctrl
    (fun ({ name; value } : _ Parse.sum_var) ->
      let disc = Oo.id (object end) in
      match value with
      | Some (field_type_pos, field_type) ->
          let+ field_type = exec_expr field_type scopes in
          let field_type = Some (expect_type field_type_pos field_type) in
          { name; disc; field_type }
      | None -> return { name; disc; field_type = None })
    variants
  >>= fun variants -> return (Type (Sum variants))

and exec_prod pos { rec'; fields } scopes : (prod, type') Either.t ctrl =
  let fields' =
    Option.map (fun (_, fields, _) -> fields)
    @@ try_fold_left
         (fun (prev_kind, fields, scope) (field : _ Parse.prod_field) ->
           match field with
           | Parse.Decl
               {
                 kind;
                 name_or_count = name_pos, Name name;
                 value = Some value;
                 _;
               } ->
               Some
                 (let kind =
                    Option.value (Option.map snd kind) ~default:prev_kind
                  in
                  let () =
                    match
                      List.find_opt (( = ) name)
                        (List.filter_map
                           (function
                             | Either.Left (_, name, _) -> Some name
                             | Either.Right _ -> None)
                           fields)
                    with
                    | Some name -> raise (Redeclaration (name_pos, name))
                    | None -> ()
                  in
                  (kind, fields @ [ Either.Left (kind, name, value) ], scope))
           | Decl { value = None; _ } -> None
           | Value (_, value) ->
               Some
                 (prev_kind, fields @ [ Either.Right (prev_kind, value) ], scope)
           | _ -> raise TODO)
         (Parse.Val, [], StringMap.empty)
         fields
  in
  let prod_of_fields fields =
    let* fields =
      map_ctrl
        (function
          | Either.Left (kind, name, value) ->
              let* value = exec_expr value scopes in
              let name = Some name in
              let entry = prod_entry value kind in
              return { name; entry }
          | Either.Right (kind, value) ->
              let* value = exec_expr value scopes in
              let entry = prod_entry value kind in
              return { name = None; entry })
        fields
    in
    return (Either.Left fields)
  in
  let prod_of_fields_rec fields =
    let scope = ref StringMap.empty in
    let lazies =
      List.map
        (function
          | Either.Left (kind, name, value) ->
              Either.Left (kind, name, lazy (exec_expr value (scope :: scopes)))
          | Either.Right (kind, value) ->
              Either.Right (kind, lazy (exec_expr value (scope :: scopes))))
        fields
    in
    let () =
      List.iter
        (function
          | Either.Left (_, name, value) ->
              scope := StringMap.add name (Dyn value) !scope;
              ()
          | Either.Right _ -> ())
        lazies
    in
    let* fields =
      map_ctrl
        (function
          | Either.Left (kind, name, (lazy value)) ->
              let* value = value in
              let name = Some name in
              let entry = prod_entry value kind in
              return { name; entry }
          | Either.Right (kind, (lazy value)) ->
              let* value = value in
              let entry = prod_entry value kind in
              return { name = None; entry })
        lazies
    in
    return (Either.Left fields)
  in
  get_or_else
    (Option.map (if rec' then prod_of_fields_rec else prod_of_fields) fields')
  @@ fun () ->
  let prod_type =
    Option.map
      (( <$> ) (fun x : (_, type') Either.t ->
           let field_types = snd x in
           Either.Right (Prod field_types)))
    @@ try_fold_left_ctrl
         (fun (prev_kind, fields) (field : _ Parse.prod_field) ->
           match field with
           | Parse.Decl { value = Some _; _ } -> None
           | Decl
               {
                 kind;
                 name_or_count = name_pos, Name name;
                 type' = Some (type_pos, type');
                 value = None;
               } ->
               Some
                 (let kind =
                    Option.value (Option.map snd kind) ~default:prev_kind
                  in
                  let () =
                    match
                      List.find_opt (( = ) name)
                        (List.map
                           (fun ({ name; _ } : prod_field_type) -> name)
                           fields)
                    with
                    | Some name -> raise (Redeclaration (name_pos, name))
                    | None -> ()
                  in
                  let+ type' = exec_expr type' scopes in
                  let type' = expect_type type_pos type' in
                  (kind, fields @ [ { kind; name; type' } ]))
           | Value _ -> None
           | _ -> raise TODO)
         (Parse.Val, []) fields
  in
  get_or_else prod_type @@ fun () -> raise (NeitherValueNorTypeProd pos)

and exec_arg_types { fields; _ } scopes =
  let+ _, args =
    fold_left_ctrl
      (fun (prev_kind, args) (arg : _ Parse.prod_field) ->
        match arg with
        | Parse.Decl
            {
              kind;
              name_or_count = name_pos, Name name;
              type' = Some (type_pos, type');
              value = None;
            } ->
            let kind = Option.value (Option.map snd kind) ~default:prev_kind in
            let+ type_val = exec_expr type' scopes in
            let () =
              match
                List.find_opt
                  (fun ({ name = existing_name; _ } : prod_field_type) ->
                    existing_name = name)
                  args
              with
              | Some { name; _ } -> raise (Redeclaration (name_pos, name))
              | None -> ()
            in
            let type' = expect_type type_pos type_val in
            (kind, args @ [ { kind; name; type' } ])
        | _ -> raise TODO)
      (Parse.Val, []) fields
  in
  args

and exec_block scopes = function
  | [ Expr expr ] -> exec_expr expr (ref StringMap.empty :: scopes)
  | [ stmt ] ->
      let+ _ = exec_stmt stmt (ref StringMap.empty :: scopes) in
      unit_val
  | stmts ->
      let+ _ = exec_nonsingle_block stmts (ref StringMap.empty :: scopes) in
      unit_val

and exec_nonsingle_block stmts scopes =
  match stmts with
  | stmt :: stmts ->
      let* _ = exec_stmt stmt scopes in
      exec_nonsingle_block stmts scopes
  | [] -> return ()

(* scopes must be non-empty. *)
and exec_stmt stmt scopes =
  match stmt with
  | Parse.Brk pos -> Brk pos
  | Ctn pos -> Ctn pos
  | Ret (pos, value) -> begin
      match value with
      | Some value ->
          let* value = exec_expr value scopes in
          Ret (pos, Some value)
      | None -> Ret (pos, None)
    end
  | Decl (decl_pos, { kind; name = name_pos, name; value; _ }) -> begin
      match (kind, value) with
      | _, Some value ->
          let+ value = exec_expr value scopes in
          let entry = scope_entry value kind in
          let scope = List.hd scopes in
          let () =
            match StringMap.find_opt name !scope with
            | Some _ -> raise (Redeclaration (name_pos, name))
            | None -> ()
          in
          scope := StringMap.add name entry !scope;
          ()
      | Mut, None ->
          let scope = List.hd scopes in
          let () =
            match StringMap.find_opt name !scope with
            | Some _ -> raise (Redeclaration (name_pos, name))
            | None -> ()
          in
          scope := StringMap.add name (Mut (ref Option.None)) !scope;
          return ()
      | Val, None -> raise (UninitializedVal (decl_pos, name))
    end
  | Assign { assignee; value } -> begin
      match assignee with
      | Id (pos, i) -> begin
          match
            List.find_map (fun scope -> StringMap.find_opt i !scope) scopes
          with
          | Some (Mut value_ref) ->
              let+ value = exec_expr value scopes in
              value_ref := Some (copy value);
              ()
          | Some _ -> raise (ImmutableAssign (pos, i))
          | None -> raise (UnboundIdent (pos, i))
        end
      | Binop (pos, accessee, Dot, _, Id (accessor_pos, accessor)) -> begin
          let* accessee = exec_expr accessee scopes in
          match deref_mut accessee with
          | Prod fields -> begin
              match
                List.find_opt (fun { name; _ } -> name = Some accessor) fields
              with
              | Some { entry = Mut value_ref; _ } ->
                  let+ value = exec_expr value scopes in
                  value_ref := Some (copy value);
                  ()
              | Some _ -> raise (ImmutableAssign (pos, accessor))
              | None -> raise (InvalidField (accessor_pos, accessor))
            end
          | invalid -> raise (InvalidAccessee (pos, invalid))
        end
      | _ -> raise TODO
    end
  | Loop body -> exec_loop body scopes
  | Expr expr ->
      let+ _ = exec_expr expr scopes in
      ()

and exec_loop body scopes =
  match exec_expr body scopes with
  | Brk _ -> return ()
  | Ret (pos, value) -> Ret (pos, value)
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
  | Ref { kind; value = Singleton { contents } } ->
      "&"
      ^ (match kind with Parse.Val -> "" | Parse.Mut -> "mut ")
      ^ stringify contents
  | Ref { value = Array { contents }; _ } ->
      if contents = [] then "[]"
      else begin
        match string_of_char_ref_array contents with
        | Some s -> "\"" ^ String.escaped s ^ "\""
        | None -> raise TODO
      end
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
      | Ref type' -> "&" ^ stringify (Type type')
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
  stringify (Proc (fun _ _ -> unit_val)) |> print_endline;
  [%expect "proc(...) { ... }"]

let%expect_test _ =
  stringify (Ref { kind = Parse.Val; value = Singleton (ref (Num 10)) })
  |> print_endline;
  [%expect "&10"]

let%expect_test _ =
  stringify (Ref { kind = Parse.Val; value = Array (ref []) }) |> print_endline;
  [%expect "[]"]

let%expect_test _ =
  stringify
    (Ref
       {
         kind = Parse.Val;
         value = Array (ref [ Rune 'a'; Rune 'b'; Rune 'c' ]);
       })
  |> print_endline;
  [%expect {|"abc"|}]

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

exception ImportInExecString of pos

let import exec_ast args =
  Val
    (Proc
       (fun call_pos fields ->
         let call_dir =
           match call_pos with
           | StringPos _ -> raise (ImportInExecString call_pos)
           | FilePos { path; _ } -> Filename.dirname path
         in
         let invalid_call_args =
           InvalidCallArgs (call_pos, [ "path" ], fields)
         in
         match fields with
         | [
          {
            name = None | Some "path";
            entry = Val (Ref { kind = Parse.Val; value = Array { contents } });
          };
         ] ->
             let relative_path =
               get_or_else (string_of_char_ref_array contents) (fun () ->
                   raise invalid_call_args)
             in
             let ast = Parse.parse (Filename.concat call_dir relative_path) in
             let ast = Parse.map_ast (fun pos -> FilePos pos) ast in
             exec_ast ast args
         | _ -> raise invalid_call_args))

let println =
  Val
    (Proc
       (fun call_pos fields ->
         match fields with
         | [ { name = None | Some "value"; entry = Val value } ] ->
             let () = stringify value |> print_endline in
             unit_val
         | _ -> raise (InvalidCallArgs (call_pos, [ "value" ], fields))))

exception OutOfBounds of pos * int * int

let () =
  Printexc.register_printer @@ function
  | OutOfBounds (pos, index, length) ->
      Some
        (Printf.sprintf "%s: out of bounds at index %d of %d element array"
           (string_of_pos pos) index length)
  | _ -> None

let _get =
  Val
    (Proc
       (fun call_pos fields ->
         match fields with
         | [
             {
               name = None;
               entry =
                 Val (Ref { kind = Parse.Val; value = Array { contents } });
             };
             { name = None; entry = Val (Num index) };
           ]
         | [
             {
               name = None | Some "array";
               entry =
                 Val (Ref { kind = Parse.Val; value = Array { contents } });
             };
             { name = Some "index"; entry = Val (Num index) };
           ] -> begin
             match List.nth_opt contents index with
             | Some value -> value
             | None ->
                 raise (OutOfBounds (call_pos, index, List.length contents))
           end
         | _ -> raise (InvalidCallArgs (call_pos, [ "array"; "index" ], fields))))

let _len =
  Val
    (Proc
       (fun call_pos fields ->
         match fields with
         | [
          {
            name = None | Some "array";
            entry = Val (Ref { kind = Parse.Val; value = Array { contents } });
          };
         ] ->
             Num (List.length contents)
         | _ -> raise (InvalidCallArgs (call_pos, [ "array" ], fields))))

let _read_file =
  Val
    (Proc
       (fun call_pos fields ->
         let invalid_call_args =
           InvalidCallArgs (call_pos, [ "path" ], fields)
         in
         match fields with
         | [
          {
            name = None | Some "path";
            entry = Val (Ref { kind = Parse.Val; value = Array { contents } });
          };
         ] ->
             let p =
               get_or_else (string_of_char_ref_array contents) (fun () ->
                   raise invalid_call_args)
             in
             let f = open_in_bin p in
             let s = really_input_string f (in_channel_length f) in
             close_in f;
             ref_array_of_string s
         | _ -> raise invalid_call_args))

let _args args =
  Val
    (Ref
       {
         kind = Parse.Val;
         value = Array (ref (List.map ref_array_of_string args));
       })

let rec exec_ast ast args =
  let builtins =
    StringMap.empty
    |> StringMap.add "false" (Val (bool_from_bool false))
    |> StringMap.add "true" (Val (bool_from_bool true))
    |> StringMap.add "num" (Val (Type Num))
    |> StringMap.add "rune" (Val (Type Rune))
    |> StringMap.add "println" println
    |> StringMap.add "import" (import exec_ast args)
    |> StringMap.add "_args" (_args args)
    |> StringMap.add "_get" _get |> StringMap.add "_len" _len
    |> StringMap.add "_readFile" _read_file
  in
  let ctrl = exec_expr ast [ ref builtins ] in
  match ctrl with
  | None value -> value
  | Brk pos | Ctn pos | Ret (pos, _) -> raise (UnexpectedCtrl pos)

let exec_string s =
  let ast = Parse.parse_string s in
  let ast = Parse.map_ast (fun pos -> StringPos pos) ast in
  exec_ast ast []

exception ExpectedProc
exception UnexpectedReturnValue

let exec path args =
  let ast = Parse.parse path in
  let ast = Parse.map_ast (fun pos -> FilePos pos) ast in
  let _ =
    match exec_ast ast args with
    | Proc f -> begin
        match f (FilePos (Starpath.FilePos.pos0 path)) [] with
        | Num n -> exit n
        | v when v = unit_val -> ()
        | _ -> raise UnexpectedReturnValue
      end
    | _ -> raise ExpectedProc
  in
  ()

let assert_raises = OUnit2.assert_raises
let%test _ = Num 14 = exec_string "5 + 9"
let%test _ = Rune 'c' = exec_string "'c'"

let%test _ =
  Ref { kind = Parse.Val; value = Array (ref [ Rune 'f'; Rune 'o'; Rune 'o' ]) }
  = exec_string {|"foo"|}

let%test _ = Rune 'o' = exec_string {|_get("foo", 1)|}
let%test _ = Num 3 = exec_string {|_len("foo")|}

let%test _ =
  Ref { kind = Parse.Val; value = Singleton (ref (Num 50)) } = exec_string "&50"

let%test _ =
  Ref { kind = Parse.Mut; value = Singleton (ref (Num 50)) }
  = exec_string "&mut 50"

let%test _ = Num 50 = exec_string "*&50"

let%test_unit _ =
  let f () = exec_string "5 == true" in
  assert_raises
    (InvalidBinopOperands
       (StringPos { row = 1; col = 1 }, Num 5, bool_from_bool true))
    f

let%test_unit _ =
  let f () = exec_string "false + true" in
  assert_raises
    (InvalidBinopOperands
       ( StringPos { row = 1; col = 1 },
         bool_from_bool false,
         bool_from_bool true ))
    f

let%test _ = Num (-4) = exec_string "5 - 9"

let%test_unit _ =
  let f () = exec_string "false - true" in
  assert_raises
    (InvalidBinopOperands
       ( StringPos { row = 1; col = 1 },
         bool_from_bool false,
         bool_from_bool true ))
    f

let%test _ = Num 45 = exec_string "5 * 9"

let%test_unit _ =
  let f () = exec_string "false * true" in
  assert_raises
    (InvalidBinopOperands
       ( StringPos { row = 1; col = 1 },
         bool_from_bool false,
         bool_from_bool true ))
    f

let%test _ = Num 0 = exec_string "5 / 9"

let%test_unit _ =
  let f () = exec_string "false / true" in
  assert_raises
    (InvalidBinopOperands
       ( StringPos { row = 1; col = 1 },
         bool_from_bool false,
         bool_from_bool true ))
    f

let%test _ = Num 5 = exec_string "5 % 9"

let%test_unit _ =
  let f () = exec_string "false % true" in
  assert_raises
    (InvalidBinopOperands
       ( StringPos { row = 1; col = 1 },
         bool_from_bool false,
         bool_from_bool true ))
    f

let%test _ = bool_from_bool false = exec_string "true && false"
let%test _ = bool_from_bool true = exec_string "true && true"

let%test_unit _ =
  let f () = exec_string "5 && 9" in
  assert_raises
    (InvalidBinopOperands (StringPos { row = 1; col = 1 }, Num 5, Num 9))
    f

let%test _ = bool_from_bool true = exec_string "false || true"
let%test _ = bool_from_bool true = exec_string "true || false"
let%test _ = bool_from_bool false = exec_string "false || false"

let%test_unit _ =
  let f () = exec_string "5 || 9" in
  assert_raises
    (InvalidBinopOperands (StringPos { row = 1; col = 1 }, Num 5, Num 9))
    f

let%test _ = bool_from_bool true = exec_string "!false"
let%test _ = bool_from_bool false = exec_string "!true"
let%test _ = bool_from_bool false = exec_string "!!!true"

let%test_unit _ =
  let f () = exec_string "!5" in
  assert_raises (InvalidUnaryOperand (StringPos { row = 1; col = 1 }, Num 5)) f

let%test _ = Num (-5) = exec_string "-5"
let%test _ = Num 5 = exec_string "--5"

let%test_unit _ =
  let f () = exec_string "-false" in
  assert_raises
    (InvalidUnaryOperand (StringPos { row = 1; col = 1 }, bool_from_bool false))
    f

let%test _ = bool_from_bool false = exec_string "false == true"
let%test _ = bool_from_bool true = exec_string "true == true"
let%test _ = bool_from_bool false = exec_string "5 == 9"
let%test _ = bool_from_bool true = exec_string "5 == 5"
let%test _ = bool_from_bool false = exec_string "'r' == 'q'"
let%test _ = bool_from_bool true = exec_string "'r' == 'r'"
let%test _ = bool_from_bool true = exec_string "false != true"
let%test _ = bool_from_bool false = exec_string "true != true"
let%test _ = bool_from_bool true = exec_string "5 != 9"
let%test _ = bool_from_bool false = exec_string "5 != 5"
let%test _ = bool_from_bool true = exec_string "'r' != 'q'"
let%test _ = bool_from_bool false = exec_string "'r' != 'r'"
let%test _ = bool_from_bool true = exec_string "5 <= 5"
let%test _ = bool_from_bool false = exec_string "9 <= 5"
let%test _ = bool_from_bool false = exec_string "'r' <= 'q'"
let%test _ = bool_from_bool true = exec_string "'q' <= 'q'"

let%test_unit _ =
  let f () = exec_string "false <= true" in
  assert_raises
    (InvalidBinopOperands
       ( StringPos { row = 1; col = 1 },
         bool_from_bool false,
         bool_from_bool true ))
    f

let%test _ = bool_from_bool false = exec_string "5 < 5"
let%test _ = bool_from_bool true = exec_string "5 < 9"
let%test _ = bool_from_bool false = exec_string "'r' < 'r'"
let%test _ = bool_from_bool true = exec_string "'q' <= 'r'"

let%test_unit _ =
  let f () = exec_string "false < true" in
  assert_raises
    (InvalidBinopOperands
       ( StringPos { row = 1; col = 1 },
         bool_from_bool false,
         bool_from_bool true ))
    f

let%test _ = Num 5 = exec_string "if true then 5 else 9"
let%test _ = Num 9 = exec_string "if false then 5 else 9"
let%test _ = unit_val = exec_string "if false then 5"

let%test_unit _ =
  let f () = exec_string "if 9 then 5 else 9" in
  assert_raises (InvalidIfCond (StringPos { row = 1; col = 4 }, Num 9)) f

let%test _ = unit_val = exec_string "()"

let%test _ =
  Prod [ { name = Some "i"; entry = Val (Num 9) } ] = exec_string "(val i = 9)"

let%test_unit _ =
  let f () = exec_string "(val i = 9, val i = 9)" in
  assert_raises (Redeclaration (StringPos { row = 1; col = 17 }, "i")) f

let%test _ =
  Prod
    [
      { name = Some "i"; entry = Val (Num 9) };
      { name = Some "j"; entry = Val (Rune 'a') };
      { name = Some "k"; entry = Mut (ref (Some (bool_from_bool true))) };
    ]
  = exec_string "(val i = 9, val j = 'a', mut k = true)"

let%test _ = Num 9 = exec_string "(val i = 9).i"
let%test _ = Rune 'a' = exec_string "(val i = 9, val j = 'a', mut k = true).j"

let%test _ =
  bool_from_bool true = exec_string "(val i = 9, val j = 'a', mut k = true).k"

let%test _ =
  bool_from_bool true = exec_string "(val i = 9, val j = 'a', mut k = true).k"

let%test_unit _ =
  let f () = exec_string "().i" in
  assert_raises (InvalidField (StringPos { row = 1; col = 4 }, "i")) f

let%test_unit _ =
  let f () = exec_string "1.i" in
  assert_raises (InvalidAccessee (StringPos { row = 1; col = 1 }, Num 1)) f

let%test _ = Type (Sum []) = exec_string "[]"

let%test _ =
  match exec_string "[Red, Green(num), Blue(rune)]" with
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
  match exec_string "[Red].Red" with
  | SumVariant { field = None; _ } -> true
  | _ -> false

let%test _ =
  match exec_string "[Green(num)].Green(value = 5)" with
  | SumVariant { field = Some (Num 5); _ } -> true
  | _ -> false

let%test_unit _ =
  let f () = exec_string "[Green(num)].Green(foo = 5)" in
  assert_raises
    (InvalidCallArgs
       ( StringPos { row = 1; col = 1 },
         [ "value" ],
         [ { name = Some "foo"; entry = Val (Num 5) } ] ))
    f

let%test_unit _ =
  let f () = exec_string "[].Blue" in
  assert_raises (InvalidField (StringPos { row = 1; col = 4 }, "Blue")) f

let%test _ =
  (*
  The two sums are separate, so the variants aren't equal though they happen to
  have the same names
  *)
  bool_from_bool false = exec_string "[Red].Red == [Red].Red"

let%test _ =
  bool_from_bool true
  = exec_string
      {|
    proc() {
      val sum = [Red, Green, Blue]
      ret sum.Green == sum.Green
    }()
  |}

let%test _ =
  bool_from_bool true
  = exec_string
      {|
    proc() {
      val sum = [Red, Green(num), Blue]
      ret sum.Green(value = 5) == sum.Green(value = 5)
    }()
  |}

let%test _ =
  bool_from_bool false
  = exec_string
      {|
    proc() {
      val sum = [Red, Green(num), Blue]
      ret sum.Green(value = 5) == sum.Green(value = 9)
    }()
  |}

let%test _ =
  bool_from_bool false
  = exec_string
      {|
    proc() {
      val sum = [Red, Green(num), Blue(num)]
      ret sum.Green(value = 5) == sum.Blue(value = 5)
    }()
  |}

let%test_unit _ =
  let f () = exec_string "[Blue(5)]" in
  assert_raises (ValueAsType (StringPos { row = 1; col = 7 }, Num 5)) f

let%test _ =
  Type (Prod [ { kind = Parse.Val; name = "foo"; type' = Num } ])
  = exec_string "(foo: num)"

let%test _ = unit_val = exec_string "{ proc() { } }()"
let%test _ = Num 3 = exec_string "{ proc(val i: Nat) { i + 1 } }(2)"

let%test _ =
  Num 18
  = exec_string
      "{ proc(val i: Nat, val j: Nat) { i * j } }(val i = 2, val j = 9)"

let%test _ =
  Num 18 = exec_string "{ proc(val i, j: Nat) { i * j } }(val i = 2, val j = 9)"

let%test_unit _ =
  let f () = exec_string "{ proc(val i: Nat) { i } }(val j = 2)" in
  assert_raises
    (InvalidCallArgs
       ( StringPos { row = 1; col = 1 },
         [ "i" ],
         [ { name = Some "j"; entry = Val (Num 2) } ] ))
    f

let%test_unit _ =
  let f () = exec_string "{ proc(val i: Nat) { i } }()" in
  assert_raises
    (InvalidCallArgs (StringPos { row = 1; col = 1 }, [ "i" ], []))
    f

let%test_unit _ =
  let f () = exec_string "proc(mut i: Nat) { i }" in
  assert_raises (MutArgument (StringPos { row = 1; col = 6 })) f

let%test_unit _ =
  let f () = exec_string "proc(val 5: Nat) { }" in
  assert_raises (NumAsArgumentName (StringPos { row = 1; col = 10 })) f

let%test_unit _ =
  let f () = exec_string "proc('a') { }" in
  assert_raises (ValueAsArgument (StringPos { row = 1; col = 6 })) f

let%test_unit _ =
  let f () = exec_string "{ proc() { foo } }()" in
  assert_raises (UnboundIdent (StringPos { row = 1; col = 12 }, "foo")) f

let%test _ =
  Num 2
  = exec_string
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

let%test_unit _ =
  let f () =
    exec_string
      {|
    {
      proc() {
        mut i
        ret i
      }
    }()
  |}
  in
  assert_raises
    (UseBeforeInitialization (StringPos { row = 5; col = 13 }, "i"))
    f

let%test _ =
  bool_from_bool true
  = exec_string
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

let%test _ = Rune 'a' = exec_string "{ proc() { loop { ret 'a' } } }()"

let%test _ =
  Num 9
  = exec_string
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

let%test_unit _ =
  let f () = exec_string "{ proc() { brk } }()" in
  assert_raises (UnexpectedCtrl (StringPos { row = 1; col = 12 })) f

let%test_unit _ =
  let f () = exec_string "{ proc() { ctn } }()" in
  assert_raises (UnexpectedCtrl (StringPos { row = 1; col = 12 })) f

let%test _ = Num 5 = exec_string "{ proc() { { ret 5 }.foo } }()"
let%test _ = Num 5 = exec_string "{ proc() { { ret 5 }() } }()"
let%test _ = Num 5 = exec_string "{ proc() { { ret 5 } + 1 } }()"
let%test _ = Num 5 = exec_string "{ proc() { 1 + { ret 5 } } }()"

let%test_unit _ =
  let f () = exec_string "1()" in
  assert_raises (InvalidCallee (StringPos { row = 1; col = 1 }, Num 1)) f

let%test _ = unit_val = exec_string "{ proc() { mut i } }()"
let%test _ = unit_val = exec_string "{ proc() { ret } }()"

let%test_unit _ =
  let f () =
    exec_string
      {|
    {
      proc() {
        val i = 1
        val i = 1
      }
    }()
  |}
  in
  assert_raises (Redeclaration (StringPos { row = 5; col = 13 }, "i")) f

let%test_unit _ =
  let f () =
    exec_string
      {|
    {
      proc() {
        mut i
        mut i
      }
    }()
  |}
  in
  assert_raises (Redeclaration (StringPos { row = 5; col = 13 }, "i")) f

let%test_unit _ =
  let f () = exec_string "{ proc() { val i } }()" in
  assert_raises (UninitializedVal (StringPos { row = 1; col = 12 }, "i")) f

let%test_unit _ =
  let f () =
    exec_string
      {|
    {
      proc() {
        val i = 1
        i = 2
      }
    }()
  |}
  in
  assert_raises (ImmutableAssign (StringPos { row = 5; col = 9 }, "i")) f

let%test_unit _ =
  let f () =
    exec_string {|
    {
      proc() {
        i = 1
      }
    }()
  |}
  in
  assert_raises (UnboundIdent (StringPos { row = 4; col = 9 }, "i")) f

let%test_unit _ =
  let f () = exec_string "{ brk }" in
  assert_raises (UnexpectedCtrl (StringPos { row = 1; col = 3 })) f

let%test_unit _ =
  let f () = exec_string "{ ctn }" in
  assert_raises (UnexpectedCtrl (StringPos { row = 1; col = 3 })) f

let%test_unit _ =
  let f () = exec_string "{ ret }" in
  assert_raises (UnexpectedCtrl (StringPos { row = 1; col = 3 })) f

let%test _ =
  Num 9
  = exec_string
      {|
    {
      proc() {
        mut p = (mut f = 5)
        p.f = 9
        ret p.f
      }
    }()
  |}

let%test_unit _ =
  let f () =
    exec_string
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
  assert_raises (InvalidField (StringPos { row = 5; col = 11 }, "bogus")) f

let%test_unit _ =
  let f () =
    exec_string
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
  assert_raises (InvalidAccessee (StringPos { row = 5; col = 9 }, Num 1)) f

let%test _ =
  Type (Proc { arg_types = []; return_type = Num }) = exec_string "proc(): num"

let%test _ =
  Type
    (Proc
       {
         arg_types = [ { kind = Parse.Val; name = "foo"; type' = Num } ];
         return_type = Num;
       })
  = exec_string "proc(foo: num): num"

let%test _ =
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
  = exec_string "proc(mut foo: num, baz: rune): num"

let%test_unit _ =
  let f () = exec_string "proc(i: num, i: num): num" in
  assert_raises (Redeclaration (StringPos { row = 1; col = 14 }, "i")) f

let%test_unit _ =
  let f () = exec_string "proc(i: num)" in
  assert_raises (ProcTypeWithoutReturn (StringPos { row = 1; col = 1 })) f

let%test _ = Num (5 + 3) = exec_string "rec (foo = 5, bar = foo + 3).bar"
let%test _ = Num (5 + 3) = exec_string "rec (foo = bar + 3, bar = 5).foo"

let%test _ =
  Num 1
  = exec_string "proc() { (foo = 2, bar = { ret 1 }, baz = { ret 0 }).foo }()"

let%test _ =
  Num 0
  = exec_string
      "proc() { rec (foo = baz, bar = { ret 1 }, baz = { ret 0 }).foo }()"

let%test _ =
  Num 1
  = exec_string
      {|
    proc() {
      val a = 1
      ret (a = 0, b = a).b
    }()
  |}

let%test _ =
  Num 0
  = exec_string
      {|
    proc() {
      val a = 1
      ret rec (a = 0, b = a).b
    }()
  |}

let%test _ =
  Num 0
  = exec_string
      {|
    proc() {
      val t = (mut field : num)
      val o = (mut field = 0)
      val f = proc(x : t) { x.field = 1 }
      f(o)
      ret o.field
    }()
  |}

let%test _ =
  Num 1
  = exec_string
      {|
    proc() {
      val t = (mut field : num)
      val o = (mut field = 0)
      val f = proc(x : &mut t) { x.field = 1 }
      f(&mut o)
      ret o.field
    }()
  |}
