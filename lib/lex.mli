type keyword = If | Then | Else | Mut | Val | Loop | Proc | Brk | Ctn | Ret
[@@deriving variants]

val string_of_keyword : keyword -> string

type token =
  | Num of int
  | Rune of char
  | String of string
  | Id of string
  | Keyword of keyword
  | Nl
  | Semi
  | OpenRound
  | CloseRound
  | OpenSquare
  | CloseSquare
  | OpenCurly
  | CloseCurly
  | Comma
  | Colon
  | Assign
  | Plus
  | Mins
  | Astr
  | Slsh
  | Perc
  | LNot
  | LAnd
  | LOr
  | Eq
  | Ne
  | Le
  | Lt
  | Dot
[@@deriving variants]

val string_of_token : token -> string
val num_expected : string
val rune_expected : string
val string_expected : string
val id_expected : string
val lex : string -> (Starpath.char_pos * token) Seq.t

exception LexError of string
