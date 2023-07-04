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
[@@deriving show]

(* both fields are one-indexed *)
type pos = { row : int; col : int }

val lex : string -> (token * pos) list
