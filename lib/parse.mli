type kind = Mut | Val
type lit = Num of int | Rune of char | String of string
type name_or_count = Name of string | Count of int
type uop = Not | UnaryMins | Ref | Deref

type binop =
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

type 'p expr =
  | Lit of lit
  | Id of 'p * string
  | Uop of 'p * uop * 'p expr
  | Binop of 'p * 'p expr * binop * 'p * 'p expr
  | If of 'p if'
  | Sum of 'p sum_var list
  | Prod of 'p prod_field list
  | Block of 'p stmt list
  | Proc of 'p proc
  | ProcT of 'p * 'p proc_t
  | Call of 'p * 'p call

and 'p if' = {
  cond : 'p * 'p expr;
  if_branch : 'p expr;
  else_branch : 'p expr option;
}

and 'p sum_var = { name : string; value : ('p * 'p expr) option }
and 'p prod_field = Decl of 'p decl_field | Value of 'p * 'p expr

and 'p decl_field = {
  kind : ('p * kind) option;
  name_or_count : 'p * name_or_count;
  type' : ('p * 'p expr) option;
  value : 'p expr option;
}

and 'p stmt =
  | Brk of 'p
  | Ctn of 'p
  | Ret of 'p * 'p expr option
  | Decl of 'p * 'p decl
  | Assign of 'p assign
  | Loop of 'p expr
  | Expr of 'p expr

and 'p decl = {
  kind : kind;
  name : 'p * string;
  type' : 'p expr option;
  value : 'p expr option;
}

and 'p assign = { assignee : 'p expr; value : 'p expr }
and 'p proc = { type' : 'p proc_t; body : 'p stmt list }

and 'p proc_t = {
  args : 'p prod_field list;
  return_type : ('p * 'p expr) option;
}

and 'p call = { callee : 'p expr; args : 'p prod_field list }

type 'p ast = 'p expr

val map_ast : ('p1 -> 'p2) -> 'p1 ast -> 'p2 ast
val parse : string -> Starpath.file_pos ast
val parse_string : string -> Starpath.string_pos ast
