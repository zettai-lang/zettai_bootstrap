type 'a with_pos = { inner : 'a; pos : Lex.pos }
type kind = Pre | Val | Var

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

and proc = { type_' : proc_type; body : stmt with_pos list }
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

type ast = expr with_pos

val parse : string -> ast
