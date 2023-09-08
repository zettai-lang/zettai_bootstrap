type keyword = Brk | Ctn | Else | If | Loop | Mut | Proc | Ret | Val
[@@deriving show]

type token =
  | Ident of string
  | Keywd of keyword
  | Num of int
  | String of string
  | Rune of char
  | Assign
  | Plus
  | Mins
  | Astr
  | Slsh
  | Perc
  | And
  | Or
  | Not
  | Eq
  | Ne
  | Le
  | Lt
  | OpenParen
  | CloseParen
  | OpenSquareBrkt
  | CloseSquareBrkt
  | OpenCurlyBrkt
  | CloseCurlyBrkt
  | Colon
  | Dot
  | Comma
  | Nl
[@@deriving show]

type pos = { path : string; row : int; col : int }

val pp_pos : Format.formatter -> pos -> unit

type lex_result = { tokens : (token * pos) list; end_pos : pos }

val lex : string -> string -> lex_result
