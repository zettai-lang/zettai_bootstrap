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

exception UnexpectedChar of char * int * int

let string_tail = function
  | "" -> ""
  | non_empty -> String.sub non_empty 1 (String.length non_empty - 1)

[@@@coverage off]

let%test _ = string_tail "" = ""
let%test _ = string_tail "f" = ""
let%test _ = string_tail "foo" = "oo"

[@@@coverage on]

let prepend_char (c : char) (s : string) = Core.Char.to_string c ^ s
let is_alpha (c : char) = ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
let is_digit (c : char) = '0' <= c && c <= '9'
let is_ident_start (c : char) = is_alpha c || c = '_'
let is_ident_rest (c : char) = is_alpha c || is_digit c || c = '_'

let rec lex_ident_rest = function
  | "" -> ("", "")
  | non_empty -> (
      match non_empty.[0] with
      | ident_char when is_ident_rest ident_char ->
          let ident_rest, text_rest = string_tail non_empty |> lex_ident_rest in
          let ident = prepend_char ident_char ident_rest in
          (ident, text_rest)
      | _ -> ("", non_empty))

[@@@coverage off]

let%test _ = lex_ident_rest "_foo651 ***" = ("_foo651", " ***")
let%test _ = lex_ident_rest "651***" = ("651", "***")
let%test _ = lex_ident_rest "" = ("", "")

[@@@coverage on]

let ident_or_keywd_of = function
  | "brk" -> Keywd Brk
  | "ctn" -> Keywd Ctn
  | "else" -> Keywd Else
  | "if" -> Keywd If
  | "loop" -> Keywd Loop
  | "pre" -> Keywd Pre
  | "proc" -> Keywd Proc
  | "ret" -> Keywd Ret
  | "val" -> Keywd Val
  | "var" -> Keywd Var
  | non_keywd -> Ident non_keywd

exception InvalidEscapeSequence of char
exception UnterminatedEscapeSequence

let lex_escape_rest (extras : char list) = function
  | "" -> raise UnterminatedEscapeSequence
  | non_empty -> (
      let tail = string_tail non_empty in
      match non_empty.[0] with
      | 'n' -> ('\n', tail)
      | 'r' -> ('\r', tail)
      | 't' -> ('\t', tail)
      | '0' -> (char_of_int 0, tail)
      | '\\' -> ('\\', tail)
      | extra when List.exists (( = ) extra) extras -> (extra, tail)
      | invalid -> InvalidEscapeSequence invalid |> raise)

let lex_char_escape_rest = lex_escape_rest [ '\\'; '\'' ]
let lex_string_escape_rest = lex_escape_rest [ '\\'; '"' ]

[@@@coverage off]

let%test _ = lex_char_escape_rest "n" = ('\n', "")
let%test _ = lex_char_escape_rest "r " = ('\r', " ")
let%test _ = lex_char_escape_rest "to" = ('\t', "o")
let%test _ = lex_char_escape_rest "0*" = (char_of_int 0, "*")
let%test _ = lex_char_escape_rest "\\'" = ('\\', "'")
let%test _ = lex_char_escape_rest "''" = ('\'', "'")
let%test _ = lex_string_escape_rest "\"'" = ('"', "'")

let%test _ =
  try
    let _ = lex_char_escape_rest "" in
    false
  with UnterminatedEscapeSequence -> true

let%test _ =
  try
    let _ = lex_char_escape_rest "\"" in
    false
  with InvalidEscapeSequence '"' -> true

let%test _ =
  try
    let _ = lex_string_escape_rest "'" in
    false
  with InvalidEscapeSequence '\'' -> true

[@@@coverage on]

exception UnterminatedString

let rec lex_string_rest = function
  | "" -> raise UnterminatedString
  | non_empty -> (
      match non_empty.[0] with
      | '"' -> ("", string_tail non_empty)
      | '\\' ->
          let escape_char, text_rest =
            string_tail non_empty |> lex_string_escape_rest
          in
          let string_rest, text_rest = lex_string_rest text_rest in
          (prepend_char escape_char string_rest, text_rest)
      | other ->
          let string_rest, text_rest =
            string_tail non_empty |> lex_string_rest
          in
          (prepend_char other string_rest, text_rest))

[@@@coverage off]

let%test _ = lex_string_rest "foo\" bar" = ("foo", " bar")
let%test _ = lex_string_rest "foo\\n\" bar" = ("foo\n", " bar")

let%test _ =
  try
    let _ = lex_string_rest "\\q" in
    false
  with InvalidEscapeSequence 'q' -> true

let%test _ =
  try
    let _ = lex_string_rest "" in
    false
  with UnterminatedString -> true

let%test _ =
  try
    let _ = lex_string_rest "foo" in
    false
  with UnterminatedString -> true

[@@@coverage on]

exception UnterminatedRune
exception EmptyRune

let lex_rune_rest = function
  | "" -> raise UnterminatedRune
  | non_empty -> (
      match non_empty.[0] with
      | '\'' -> raise EmptyRune
      | '\\' -> (
          let escape_char, text_rest =
            string_tail non_empty |> lex_char_escape_rest
          in
          match text_rest with
          | "" -> raise UnterminatedRune
          | non_empty -> (
              match non_empty.[0] with
              | '\'' -> (escape_char, string_tail text_rest)
              | _ -> raise UnterminatedRune))
      | rune_contents -> (
          let after_rune_char = string_tail non_empty in
          match after_rune_char with
          | "" -> raise UnterminatedRune
          | non_empty -> (
              match non_empty.[0] with
              | '\'' -> (rune_contents, string_tail non_empty)
              | _ -> raise UnterminatedRune)))

[@@@coverage off]

let%test _ = lex_rune_rest " 'foo" = (' ', "foo")
let%test _ = lex_rune_rest "f''''" = ('f', "'''")
let%test _ = lex_rune_rest "\\n' " = ('\n', " ")

let%test _ =
  try
    let _ = lex_rune_rest "" in
    false
  with UnterminatedRune -> true

let%test _ =
  try
    let _ = lex_rune_rest "'" in
    false
  with EmptyRune -> true

let%test _ =
  try
    let _ = lex_rune_rest "\\q" in
    false
  with InvalidEscapeSequence 'q' -> true

let%test _ =
  try
    let _ = lex_rune_rest "\\n" in
    false
  with UnterminatedRune -> true

let%test _ =
  try
    let _ = lex_rune_rest "\\nf" in
    false
  with UnterminatedRune -> true

let%test _ =
  try
    let _ = lex_rune_rest "f" in
    false
  with UnterminatedRune -> true

let%test _ =
  try
    let _ = lex_rune_rest "ff'" in
    false
  with UnterminatedRune -> true

[@@@coverage on]

exception UnterminatedAnd
exception UnterminatedOr

let rec lex = function
  | "" -> []
  | non_empty -> (
      match non_empty.[0] with
      | ' ' | '\t' | '\n' -> string_tail non_empty |> lex
      | ident_start when is_ident_start ident_start ->
          let ident_rest, text_rest = string_tail non_empty |> lex_ident_rest in
          let ident = prepend_char ident_start ident_rest in
          [ ident_or_keywd_of ident ] @ lex text_rest
      | '"' ->
          let string, text_rest = string_tail non_empty |> lex_string_rest in
          [ String string ] @ lex text_rest
      | '\'' ->
          let rune, text_rest = string_tail non_empty |> lex_rune_rest in
          [ Rune rune ] @ lex text_rest
      | '=' -> (
          let after_first_eq = string_tail non_empty in
          match after_first_eq with
          | "" -> [ Assign ]
          | non_empty -> (
              match non_empty.[0] with
              | '=' -> [ Eq ] @ lex (string_tail non_empty)
              | _ -> [ Assign ] @ lex non_empty))
      | '+' -> [ Plus ] @ lex (string_tail non_empty)
      | '-' -> [ Mins ] @ lex (string_tail non_empty)
      | '*' -> [ Astr ] @ lex (string_tail non_empty)
      | '/' -> [ Slsh ] @ lex (string_tail non_empty)
      | '%' -> [ Perc ] @ lex (string_tail non_empty)
      | '&' -> (
          let after_first_and = string_tail non_empty in
          match after_first_and with
          | "" -> raise UnterminatedAnd
          | non_empty -> (
              match non_empty.[0] with
              | '&' -> [ And ] @ lex (string_tail non_empty)
              | u -> UnexpectedChar (u, 0, 0) |> raise))
      | '|' -> (
          let after_first_or = string_tail non_empty in
          match after_first_or with
          | "" -> raise UnterminatedOr
          | non_empty -> (
              match non_empty.[0] with
              | '|' -> [ Or ] @ lex (string_tail non_empty)
              | u -> UnexpectedChar (u, 0, 0) |> raise))
      | '!' -> (
          let after_not = string_tail non_empty in
          match after_not with
          | "" -> [ Not ]
          | non_empty -> (
              match non_empty.[0] with
              | '=' -> [ Ne ] @ lex (string_tail non_empty)
              | _ -> [ Not ] @ lex non_empty))
      | '<' -> (
          let after_less = string_tail non_empty in
          match after_less with
          | "" -> [ Lt ]
          | non_empty -> (
              match non_empty.[0] with
              | '=' -> [ Le ] @ lex (string_tail non_empty)
              | _ -> [ Lt ] @ lex non_empty))
      | '(' -> [ OpenParen ] @ lex (string_tail non_empty)
      | ')' -> [ CloseParen ] @ lex (string_tail non_empty)
      | '[' -> [ OpenSquareBrkt ] @ lex (string_tail non_empty)
      | ']' -> [ CloseSquareBrkt ] @ lex (string_tail non_empty)
      | '{' -> [ OpenCurlyBrkt ] @ lex (string_tail non_empty)
      | '}' -> [ CloseCurlyBrkt ] @ lex (string_tail non_empty)
      | ':' -> [ Colon ] @ lex (string_tail non_empty)
      | '.' -> [ Dot ] @ lex (string_tail non_empty)
      | ',' -> [ Comma ] @ lex (string_tail non_empty)
      | u -> UnexpectedChar (u, 0, 0) |> raise)

let print_lex (text : string) =
  lex text |> List.map show_token |> String.concat "\n" |> print_endline

[@@@coverage off]

(* ident *)
let%expect_test _ =
  print_lex "_foo\t_13651\nBar_651 Iljbzlskmvk";
  [%expect
    {|
    (Lex.Ident "_foo")
    (Lex.Ident "_13651")
    (Lex.Ident "Bar_651")
    (Lex.Ident "Iljbzlskmvk")
  |}]

(* keyword *)
let%expect_test _ =
  print_lex "brk ctn else if loop pre proc ret val var";
  [%expect
    {|
    (Lex.Keywd Lex.Brk)
    (Lex.Keywd Lex.Ctn)
    (Lex.Keywd Lex.Else)
    (Lex.Keywd Lex.If)
    (Lex.Keywd Lex.Loop)
    (Lex.Keywd Lex.Pre)
    (Lex.Keywd Lex.Proc)
    (Lex.Keywd Lex.Ret)
    (Lex.Keywd Lex.Val)
    (Lex.Keywd Lex.Var)
  |}]

(* string *)
let%expect_test _ =
  print_lex "\"foo\" \"bar\\n\"";
  [%expect {|
    (Lex.String "foo")
    (Lex.String "bar\n")
  |}]

(* rune *)
let%expect_test _ =
  print_lex "'f' '\\n' '\\\\' ";
  [%expect {|
    (Lex.Rune 'f')
    (Lex.Rune '\n')
    (Lex.Rune '\\')
  |}]

(* assign *)
let%expect_test _ =
  print_lex "= =a =";
  [%expect
    {|
    Lex.Assign
    Lex.Assign
    (Lex.Ident "a")
    Lex.Assign
  |}]

(* arithmetic *)
let%expect_test _ =
  print_lex "+ - * / % ++ -- *=";
  [%expect
    {|
    Lex.Plus
    Lex.Mins
    Lex.Astr
    Lex.Slsh
    Lex.Perc
    Lex.Plus
    Lex.Plus
    Lex.Mins
    Lex.Mins
    Lex.Astr
    Lex.Assign
  |}]

(* boolean *)
let%expect_test _ =
  print_lex "&& || ! !";
  [%expect {|
    Lex.And
    Lex.Or
    Lex.Not
    Lex.Not
  |}]

let%test _ =
  try
    let _ = lex "&" in
    false
  with UnterminatedAnd -> true

let%test _ =
  try
    let _ = lex "& " in
    false
  with UnexpectedChar (' ', 0, 0) -> true

let%test _ =
  try
    let _ = lex "|" in
    false
  with UnterminatedOr -> true

let%test _ =
  try
    let _ = lex "| " in
    false
  with UnexpectedChar (' ', 0, 0) -> true

(* comparison *)
let%expect_test _ =
  print_lex "== != <= < <";
  [%expect {|
    Lex.Eq
    Lex.Ne
    Lex.Le
    Lex.Lt
    Lex.Lt
  |}]

(* open/close *)
let%expect_test _ =
  print_lex "() [] {} ( [ { ) ] }";
  [%expect
    {|
    Lex.OpenParen
    Lex.CloseParen
    Lex.OpenSquareBrkt
    Lex.CloseSquareBrkt
    Lex.OpenCurlyBrkt
    Lex.CloseCurlyBrkt
    Lex.OpenParen
    Lex.OpenSquareBrkt
    Lex.OpenCurlyBrkt
    Lex.CloseParen
    Lex.CloseSquareBrkt
    Lex.CloseCurlyBrkt
  |}]

(* punctuation *)
let%expect_test _ =
  print_lex ": . ,";
  [%expect {|
    Lex.Colon
    Lex.Dot
    Lex.Comma
  |}]

(* unexpected *)
let%test _ =
  try
    let _ = lex "$ " in
    false
  with UnexpectedChar ('$', 0, 0) -> true

[@@@coverage on]
