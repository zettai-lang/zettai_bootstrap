type keyword = Brk | Ctn | Else | If | Loop | Pre | Proc | Ret | Val | Var
[@@deriving show]

type token =
  | Ident of string
  | Keywd of keyword
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
[@@deriving show]

val lex : string -> token list
