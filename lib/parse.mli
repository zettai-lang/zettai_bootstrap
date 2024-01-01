type kind = Mut | Val

type expr =
  | Lit of lit
  | Id of string
  | Uop of uop * expr
  | Binop of expr * binop * expr
  | If of if'
  | Sum of sum_var list
  | Prod of prod_field list
  | Block of stmt list
  | Proc of proc
  | ProcT of proc_t
  | Call of call

and lit = Num of int | Rune of char | String of string
and uop = Not | UnaryMins

and binop =
  | Plus
  | Mins
  | Astr
  | Slsh
  | Perc
  | And
  | Or
  | Eq
  | Ne
  | Le
  | Lt
  | Dot

and if' = { cond : expr; if_branch : expr; else_branch : expr option }
and sum_var = { name : string; value : expr option }
and prod_field = Decl of decl_field | Value of expr

and decl_field = {
  kind : kind option;
  name_or_count : name_or_count;
  type' : expr option;
  value : expr option;
}

and name_or_count = Name of string | Count of int

and stmt =
  | Brk
  | Ctn
  | Ret of expr option
  | Decl of decl
  | Assign of assign
  | Loop of expr
  | Expr of expr

and decl = {
  kind : kind;
  name : string;
  type' : expr option;
  value : expr option;
}

and assign = { assignee : expr; value : expr }
and proc = { type' : proc_t; body : stmt list }
and proc_t = { args : prod_field list; return_type : expr option }
and call = { callee : expr; args : prod_field list }

type ast = expr

val parse : string -> ast
