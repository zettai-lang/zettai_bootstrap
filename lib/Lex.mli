type keyword = Brk | Ctn | Else | If | Loop | Pre | Proc | Ret | Val | Var
[@@deriving show]

type token =
  | Ident of string
  | Keywd of keyword
  | Bool of bool
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

type pos = { row : int; col : int }
type lex_result = { tokens : (token * pos) list; end_pos : pos }

val lex : string -> lex_result
