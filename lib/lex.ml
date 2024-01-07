type keyword = If | Then | Else | Mut | Val | Loop | Proc | Brk | Ctn | Ret
[@@deriving variants]

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

let string_of_keyword : keyword -> string = function
  | If -> "if"
  | Then -> "then"
  | Else -> "else"
  | Mut -> "mut"
  | Val -> "val"
  | Loop -> "loop"
  | Proc -> "proc"
  | Brk -> "brk"
  | Ctn -> "ctn"
  | Ret -> "ret"

let string_of_token =
  let open Util in
  (function
    | Num n -> string_of_int n
    | Rune c -> char_quoted c
    | String s -> quoted s
    | Id s -> s
    | Keyword s -> string_of_keyword s
    | Nl -> "\n"
    | Semi -> ";"
    | OpenRound -> "("
    | CloseRound -> ")"
    | OpenSquare -> "["
    | CloseSquare -> "]"
    | OpenCurly -> "{"
    | CloseCurly -> "}"
    | Comma -> ","
    | Colon -> ":"
    | Assign -> "="
    | Plus -> "+"
    | Mins -> "-"
    | Astr -> "*"
    | Slsh -> "/"
    | Perc -> "%"
    | LNot -> "!"
    | LAnd -> "&&"
    | LOr -> "||"
    | Eq -> "=="
    | Ne -> "!="
    | Le -> "<="
    | Lt -> "<"
    | Dot -> ".")
  >> quoted

let num_expected = "<NUM>"
let rune_expected = "<RUNE>"
let string_expected = "<STRING>"
let id_expected = "<ID>"

open Starpath.StringCombinators
open Util

let keywords =
  [ "if"; "then"; "else"; "mut"; "val"; "loop"; "proc"; "brk"; "ctn"; "ret" ]

let keyword' =
  string "if" *> return If
  <|> string "then" *> return Then
  <|> string "else" *> return Else
  <|> string "mut" *> return Mut
  <|> string "val" *> return Val
  <|> string "loop" *> return Loop
  <|> string "proc" *> return Proc
  <|> string "brk" *> return Brk
  <|> string "ctn" *> return Ctn
  <|> string "ret" *> return Ret

let implode = List.to_seq >> String.of_seq
let is_digit = function '0' .. '9' -> true | _ -> false

let num' =
  take_while1 ~expected:[ "\\d+" ] is_digit >>| (implode >> int_of_string)

let rune' = token '\'' *> token_not '\'' <* token '\''
let string' = token '"' *> take_while (( <> ) '"') >>| implode <* token '"'
let is_id_start = function 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false
let is_id_cont c = is_id_start c || is_digit c

let id' =
  let* pos, start = satisfy ~expected:[ "[a-zA-Z_]" ] is_id_start |> pos in
  let* rest = take_while is_id_cont in
  let id = String.make 1 start ^ implode rest in
  if List.exists (( = ) id) keywords then
    fail
      {
        pos;
        expected = [ "not " ^ String.concat " | " keywords ];
        actual = "reserved keyword: \"" ^ String.escaped id ^ "\"";
      }
  else return id

let token' =
  num'
  >>| (fun n -> Num n)
  <|> (rune' >>| fun c -> Rune c)
  <|> (string' >>| fun s -> String s)
  <|> (id' >>| fun i -> Id i)
  <|> (keyword' >>| fun k -> Keyword k)
  <|> token '\n' @> return Nl
  <|> token ';' @> return Semi
  <|> token '(' @> return OpenRound
  <|> token ')' @> return CloseRound
  <|> token '[' @> return OpenSquare
  <|> token ']' @> return CloseSquare
  <|> token '{' @> return OpenCurly
  <|> token '}' @> return CloseCurly
  <|> token ',' @> return Comma
  <|> token ':' @> return Colon
  <|> token '+' @> return Plus
  <|> token '-' @> return Mins
  <|> token '*' @> return Astr
  <|> token '/' @> return Slsh
  <|> token '%' @> return Perc
  <|> string "&&" @> return LAnd
  <|> string "||" @> return LOr
  <|> string "==" @> return Eq
  <|> token '=' @> return Assign
  <|> string "!=" @> return Ne
  <|> token '!' @> return LNot
  <|> string "<=" @> return Le
  <|> token '<' @> return Lt
  <|> token '.' @> return Dot

let white = token ' ' <|> token '\t' <|> token '\r'

let tokens =
  repeat white *> sep_by (repeat white) (token' |> pos) <* repeat white

exception LexError of string

let lex input =
  match parse_string input tokens with
  | Ok ts -> List.to_seq ts
  | Error pe -> raise (LexError (string_of_parse_error pe))
