open Ppx_compare_lib.Builtin
open Sexplib.Std

let assert_raises = OUnit2.assert_raises

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

[@@@coverage off]

type pos = { path : string; row : int; col : int } [@@deriving compare, sexp]

[@@@coverage on]

let pp_pos f p = Format.fprintf f "%d:%d" p.row p.col

[@@@coverage off]

type state = { text : string; pos : pos } [@@deriving compare, sexp]

[@@@coverage on]

let state_from text path = { text; pos = { path; row = 1; col = 1 } }

let advanced s =
  match s.text with
  | "" -> None
  | non_empty ->
      let head = non_empty.[0] in
      let tail = String.sub non_empty 1 (String.length non_empty - 1) in
      let pos =
        if head = '\n' then { s.pos with row = s.pos.row + 1; col = 1 }
        else { s.pos with col = s.pos.col + 1 }
      in
      Some (head, { text = tail; pos })

let with_advanced_or s default f =
  match advanced s with
  | None -> default
  | Some (head, advanced) -> f head advanced

let advanced_or_raise s make_exn =
  match advanced s with
  | None -> raise (make_exn s.pos)
  | Some (head, advanced) -> (head, advanced)

let expect_char s expected make_exn =
  let head, advanced = advanced_or_raise s make_exn in
  if head != expected then raise (make_exn s.pos) else advanced

let prepend_char c s = Core.Char.to_string c ^ s
let is_alpha c = ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
let is_digit c = '0' <= c && c <= '9'
let is_ident_start c = is_alpha c || c = '_'
let is_ident_rest c = is_alpha c || is_digit c || c = '_'

let rec lex_ident_rest s =
  with_advanced_or s ("", s) (fun next advanced ->
      if is_ident_rest next then
        let ident_rest, remaining = lex_ident_rest advanced in
        let ident = prepend_char next ident_rest in
        (ident, remaining)
      else ("", s))

[@@@coverage off]

type string_state_tuple = string * state [@@deriving compare, sexp]

[@@@coverage on]

let%test_unit _ =
  [%test_result: string_state_tuple]
    (state_from "_foo651 ***" "test.zt" |> lex_ident_rest)
    ~expect:
      ( "_foo651",
        { text = " ***"; pos = { path = "test.zt"; row = 1; col = 8 } } )

let%test_unit _ =
  [%test_result: string_state_tuple]
    (state_from "651***" "test.zt" |> lex_ident_rest)
    ~expect:
      ("651", { text = "***"; pos = { path = "test.zt"; row = 1; col = 4 } })

let%test_unit _ =
  [%test_result: string_state_tuple]
    (state_from "" "test.zt" |> lex_ident_rest)
    ~expect:("", { text = ""; pos = { path = "test.zt"; row = 1; col = 1 } })

let rec lex_num_rest s =
  with_advanced_or s ("", s) (fun head advanced ->
      if is_digit head then
        let num_rest, after_num = lex_num_rest advanced in
        let num = prepend_char head num_rest in
        (num, after_num)
      else ("", s))

let%test_unit _ =
  [%test_result: string_state_tuple]
    (state_from "0123456789" "test.zt" |> lex_num_rest)
    ~expect:
      ( "0123456789",
        { text = ""; pos = { path = "test.zt"; row = 1; col = 11 } } )

let%test_unit _ =
  [%test_result: string_state_tuple]
    (state_from "0123456789 ***" "test.zt" |> lex_num_rest)
    ~expect:
      ( "0123456789",
        { text = " ***"; pos = { path = "test.zt"; row = 1; col = 11 } } )

let%test_unit _ =
  [%test_result: string_state_tuple]
    (state_from "" "test.zt" |> lex_num_rest)
    ~expect:("", { text = ""; pos = { path = "test.zt"; row = 1; col = 1 } })

let ident_keywd_of = function
  | "brk" -> Keywd Brk
  | "ctn" -> Keywd Ctn
  | "else" -> Keywd Else
  | "if" -> Keywd If
  | "loop" -> Keywd Loop
  | "mut" -> Keywd Mut
  | "proc" -> Keywd Proc
  | "ret" -> Keywd Ret
  | "val" -> Keywd Val
  | non_keywd -> Ident non_keywd

exception InvalidEscapeSequence of char * pos
exception UnterminatedEscapeSequence of pos

let lex_escape_rest extras s =
  let head, advanced =
    advanced_or_raise s (fun p -> UnterminatedEscapeSequence p)
  in
  let escape_char =
    match head with
    | 'n' -> '\n'
    | 'r' -> '\r'
    | 't' -> '\t'
    | '0' -> char_of_int 0
    | '\\' -> '\\'
    | extra when List.exists (( = ) extra) extras -> extra
    | invalid -> raise (InvalidEscapeSequence (invalid, s.pos))
  in
  (escape_char, advanced)

let lex_char_escape_rest = lex_escape_rest [ '\\'; '\'' ]
let lex_string_escape_rest = lex_escape_rest [ '\\'; '"' ]

[@@@coverage off]

type char_state_tuple = char * state [@@deriving compare, sexp]

[@@@coverage on]

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "n" "test.zt" |> lex_char_escape_rest)
    ~expect:('\n', { text = ""; pos = { path = "test.zt"; row = 1; col = 2 } })

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "r " "test.zt" |> lex_char_escape_rest)
    ~expect:('\r', { text = " "; pos = { path = "test.zt"; row = 1; col = 2 } })

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "to" "test.zt" |> lex_char_escape_rest)
    ~expect:('\t', { text = "o"; pos = { path = "test.zt"; row = 1; col = 2 } })

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "0*" "test.zt" |> lex_char_escape_rest)
    ~expect:
      ( char_of_int 0,
        { text = "*"; pos = { path = "test.zt"; row = 1; col = 2 } } )

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "\\'" "test.zt" |> lex_char_escape_rest)
    ~expect:('\\', { text = "'"; pos = { path = "test.zt"; row = 1; col = 2 } })

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "''" "test.zt" |> lex_char_escape_rest)
    ~expect:('\'', { text = "'"; pos = { path = "test.zt"; row = 1; col = 2 } })

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "\"'" "test.zt" |> lex_string_escape_rest)
    ~expect:('"', { text = "'"; pos = { path = "test.zt"; row = 1; col = 2 } })

let%test_unit _ =
  let f () = state_from "" "test.zt" |> lex_char_escape_rest in
  assert_raises
    (UnterminatedEscapeSequence { path = "test.zt"; row = 1; col = 1 })
    f

let%test_unit _ =
  let f () = state_from "\"" "test.zt" |> lex_char_escape_rest in
  assert_raises
    (InvalidEscapeSequence ('"', { path = "test.zt"; row = 1; col = 1 }))
    f

let%test_unit _ =
  let f () = state_from "'" "test.zt" |> lex_string_escape_rest in
  assert_raises
    (InvalidEscapeSequence ('\'', { path = "test.zt"; row = 1; col = 1 }))
    f

exception UnterminatedString of pos

let rec lex_string_rest s =
  let head, advanced = advanced_or_raise s (fun p -> UnterminatedString p) in
  match head with
  | '"' -> ("", advanced)
  | other ->
      let unescaped, after_escape =
        if other = '\\' then lex_string_escape_rest advanced
        else (other, advanced)
      in
      let string_rest, remaining = lex_string_rest after_escape in
      (prepend_char unescaped string_rest, remaining)

let%test_unit _ =
  [%test_result: string_state_tuple]
    (state_from "foo\" bar" "test.zt" |> lex_string_rest)
    ~expect:
      ("foo", { text = " bar"; pos = { path = "test.zt"; row = 1; col = 5 } })

let%test_unit _ =
  [%test_result: string_state_tuple]
    (state_from "foo\\n\" bar" "test.zt" |> lex_string_rest)
    ~expect:
      ("foo\n", { text = " bar"; pos = { path = "test.zt"; row = 1; col = 7 } })

let%test_unit _ =
  let f () = state_from "\\q" "test.zt" |> lex_string_rest in
  assert_raises
    (InvalidEscapeSequence ('q', { path = "test.zt"; row = 1; col = 2 }))
    f

let%test_unit _ =
  let f () = state_from "" "test.zt" |> lex_string_rest in
  assert_raises (UnterminatedString { path = "test.zt"; row = 1; col = 1 }) f

let%test_unit _ =
  let f () = state_from "foo" "test.zt" |> lex_string_rest in
  assert_raises (UnterminatedString { path = "test.zt"; row = 1; col = 4 }) f

exception UnterminatedRune of pos
exception EmptyRune of pos

let lex_rune_rest s =
  let head, advanced = advanced_or_raise s (fun p -> UnterminatedRune p) in
  match head with
  | '\'' -> raise (EmptyRune s.pos)
  | rune_char ->
      let unescaped, after_escape =
        if rune_char = '\\' then lex_char_escape_rest advanced
        else (rune_char, advanced)
      in
      let after_close =
        expect_char after_escape '\'' (fun p -> UnterminatedRune p)
      in
      (unescaped, after_close)

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from " 'foo" "test.zt" |> lex_rune_rest)
    ~expect:(' ', { text = "foo"; pos = { path = "test.zt"; row = 1; col = 3 } })

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "f''''" "test.zt" |> lex_rune_rest)
    ~expect:('f', { text = "'''"; pos = { path = "test.zt"; row = 1; col = 3 } })

let%test_unit _ =
  [%test_result: char_state_tuple]
    (state_from "\\n' " "test.zt" |> lex_rune_rest)
    ~expect:('\n', { text = " "; pos = { path = "test.zt"; row = 1; col = 4 } })

let%test_unit _ =
  let f () = state_from "" "test.zt" |> lex_rune_rest in
  assert_raises (UnterminatedRune { path = "test.zt"; col = 1; row = 1 }) f

let%test_unit _ =
  let f () = state_from "'" "test.zt" |> lex_rune_rest in
  assert_raises (EmptyRune { path = "test.zt"; col = 1; row = 1 }) f

let%test_unit _ =
  let f () = state_from "\\q" "test.zt" |> lex_rune_rest in
  assert_raises
    (InvalidEscapeSequence ('q', { path = "test.zt"; row = 1; col = 2 }))
    f

let%test_unit _ =
  let f () = state_from "\\n" "test.zt" |> lex_rune_rest in
  assert_raises (UnterminatedRune { path = "test.zt"; row = 1; col = 3 }) f

let%test_unit _ =
  let f () = state_from "\\nf" "test.zt" |> lex_rune_rest in
  assert_raises (UnterminatedRune { path = "test.zt"; row = 1; col = 3 }) f

let%test_unit _ =
  let f () = state_from "f" "test.zt" |> lex_rune_rest in
  assert_raises (UnterminatedRune { path = "test.zt"; row = 1; col = 2 }) f

let%test_unit _ =
  let f () = state_from "ff'" "test.zt" |> lex_rune_rest in
  assert_raises (UnterminatedRune { path = "test.zt"; row = 1; col = 2 }) f

let rec lex_comment_rest state : state =
  with_advanced_or state state (fun head advanced ->
      match head with '\n' -> advanced | _ -> lex_comment_rest advanced)

let%test_unit _ =
  [%test_result: state]
    (state_from "" "test.zt" |> lex_comment_rest)
    ~expect:{ text = ""; pos = { path = "test.zt"; row = 1; col = 1 } }

let%test_unit _ =
  [%test_result: state]
    (state_from "\n foo bar" "test.zt" |> lex_comment_rest)
    ~expect:{ text = " foo bar"; pos = { path = "test.zt"; row = 2; col = 1 } }

let%test_unit _ =
  [%test_result: state]
    (state_from "asdf65**+%*-89651\n foo bar" "test.zt" |> lex_comment_rest)
    ~expect:{ text = " foo bar"; pos = { path = "test.zt"; row = 2; col = 1 } }

exception UnexpectedChar of char * pos

let () =
  Printexc.register_printer (function
    | UnexpectedChar (char, { path; row; col }) ->
        Some (Printf.sprintf "%s:%d:%d: unexpected char: %C" path row col char)
    | _ -> None)

exception UnterminatedAnd of pos
exception UnterminatedOr of pos

type lex_result = { tokens : (token * pos) list; end_pos : pos }
[@@deriving show]

let rec lex' s =
  with_advanced_or s { tokens = []; end_pos = s.pos } (fun head advanced ->
      let tokens, after =
        match head with
        | ' ' | '\t' -> ([], advanced)
        | '\n' -> ([ (Nl, s.pos) ], advanced)
        | ident_start when is_ident_start ident_start ->
            let ident_rest, after_ident = lex_ident_rest advanced in
            let ident = prepend_char ident_start ident_rest in
            ([ (ident_keywd_of ident, s.pos) ], after_ident)
        | num_start when is_digit num_start ->
            let num_rest, after_num = lex_num_rest advanced in
            let num = prepend_char num_start num_rest |> int_of_string in
            ([ (Num num, s.pos) ], after_num)
        | '"' ->
            let string, after_string = lex_string_rest advanced in
            ([ (String string, s.pos) ], after_string)
        | '\'' ->
            let rune, after_rune = lex_rune_rest advanced in
            ([ (Rune rune, s.pos) ], after_rune)
        | '=' ->
            with_advanced_or advanced
              ([ (Assign, s.pos) ], advanced)
              (fun head remaining ->
                if head = '=' then ([ (Eq, s.pos) ], remaining)
                else ([ (Assign, s.pos) ], advanced))
        | '+' -> ([ (Plus, s.pos) ], advanced)
        | '-' -> ([ (Mins, s.pos) ], advanced)
        | '*' -> ([ (Astr, s.pos) ], advanced)
        | '/' -> ([ (Slsh, s.pos) ], advanced)
        | '%' -> ([ (Perc, s.pos) ], advanced)
        | '&' ->
            ( [ (And, s.pos) ],
              expect_char advanced '&' (fun p -> UnterminatedAnd p) )
        | '|' ->
            ( [ (Or, s.pos) ],
              expect_char advanced '|' (fun p -> UnterminatedOr p) )
        | '!' ->
            with_advanced_or advanced
              ([ (Not, s.pos) ], advanced)
              (fun head remaining ->
                if head = '=' then ([ (Ne, s.pos) ], remaining)
                else ([ (Not, s.pos) ], advanced))
        | '<' ->
            with_advanced_or advanced
              ([ (Lt, s.pos) ], advanced)
              (fun head remaining ->
                if head = '=' then ([ (Le, s.pos) ], remaining)
                else ([ (Lt, s.pos) ], advanced))
        | '(' -> ([ (OpenParen, s.pos) ], advanced)
        | ')' -> ([ (CloseParen, s.pos) ], advanced)
        | '[' -> ([ (OpenSquareBrkt, s.pos) ], advanced)
        | ']' -> ([ (CloseSquareBrkt, s.pos) ], advanced)
        | '{' -> ([ (OpenCurlyBrkt, s.pos) ], advanced)
        | '}' -> ([ (CloseCurlyBrkt, s.pos) ], advanced)
        | ':' -> ([ (Colon, s.pos) ], advanced)
        | '.' -> ([ (Dot, s.pos) ], advanced)
        | ',' -> ([ (Comma, s.pos) ], advanced)
        | '#' -> ([], lex_comment_rest advanced)
        | u -> raise (UnexpectedChar (u, s.pos))
      in
      let { tokens = tokens_rest; end_pos } = lex' after in
      { tokens = tokens @ tokens_rest; end_pos })

let lex text path = state_from text path |> lex'

let%expect_test _ =
  lex "_foo\t_13651\nBar_651 Iljbzlskmvk" "test.zt"
  |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [((Lex.Ident "_foo"), 1:1); ((Lex.Ident "_13651"), 1:6); (Lex.Nl, 1:12);
          ((Lex.Ident "Bar_651"), 2:1); ((Lex.Ident "Iljbzlskmvk"), 2:9)];
        end_pos = 2:20 }
    |}]

let%expect_test _ =
  lex "0123456789 91555 31512 11 3" "test.zt"
  |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [((Lex.Num 123456789), 1:1); ((Lex.Num 91555), 1:12);
          ((Lex.Num 31512), 1:18); ((Lex.Num 11), 1:24); ((Lex.Num 3), 1:27)];
        end_pos = 1:28 }
    |}]

let%expect_test _ =
  lex "brk ctn else if loop mut proc ret val" "test.zt"
  |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [((Lex.Keywd Lex.Brk), 1:1); ((Lex.Keywd Lex.Ctn), 1:5);
          ((Lex.Keywd Lex.Else), 1:9); ((Lex.Keywd Lex.If), 1:14);
          ((Lex.Keywd Lex.Loop), 1:17); ((Lex.Keywd Lex.Mut), 1:22);
          ((Lex.Keywd Lex.Proc), 1:26); ((Lex.Keywd Lex.Ret), 1:31);
          ((Lex.Keywd Lex.Val), 1:35)];
        end_pos = 1:38 }
    |}]

let%expect_test _ =
  lex "\"foo\" \"bar\\n\"" "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens = [((Lex.String "foo"), 1:1); ((Lex.String "bar\n"), 1:7)];
        end_pos = 1:14 }
    |}]

let%expect_test _ =
  lex "'f' '\\n' '\\\\' " "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [((Lex.Rune 'f'), 1:1); ((Lex.Rune '\n'), 1:5); ((Lex.Rune '\\'), 1:10)];
        end_pos = 1:15 }
    |}]

let%expect_test _ =
  lex "= =a =" "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [(Lex.Assign, 1:1); (Lex.Assign, 1:3); ((Lex.Ident "a"), 1:4);
          (Lex.Assign, 1:6)];
        end_pos = 1:7 }
    |}]

let%expect_test _ =
  lex "+ - * / % ++ -- *=" "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [(Lex.Plus, 1:1); (Lex.Mins, 1:3); (Lex.Astr, 1:5); (Lex.Slsh, 1:7);
          (Lex.Perc, 1:9); (Lex.Plus, 1:11); (Lex.Plus, 1:12); (Lex.Mins, 1:14);
          (Lex.Mins, 1:15); (Lex.Astr, 1:17); (Lex.Assign, 1:18)];
        end_pos = 1:19 }
    |}]

let%expect_test _ =
  lex "&& || ! !" "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [(Lex.And, 1:1); (Lex.Or, 1:4); (Lex.Not, 1:7); (Lex.Not, 1:9)];
        end_pos = 1:10 }
    |}]

let%test_unit _ =
  let f () = lex "&" "test.zt" in
  assert_raises (UnterminatedAnd { path = "test.zt"; row = 1; col = 2 }) f

let%test_unit _ =
  let f () = lex "& " "test.zt" in
  assert_raises (UnterminatedAnd { path = "test.zt"; row = 1; col = 2 }) f

let%test_unit _ =
  let f () = lex "|" "test.zt" in
  assert_raises (UnterminatedOr { path = "test.zt"; row = 1; col = 2 }) f

let%test_unit _ =
  let f () = lex "| " "test.zt" in
  assert_raises (UnterminatedOr { path = "test.zt"; row = 1; col = 2 }) f

let%expect_test _ =
  lex "== != <= < <" "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [(Lex.Eq, 1:1); (Lex.Ne, 1:4); (Lex.Le, 1:7); (Lex.Lt, 1:10);
          (Lex.Lt, 1:12)];
        end_pos = 1:13 }
    |}]

let%expect_test _ =
  lex "() [] {} ( [ { ) ] }" "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens =
        [(Lex.OpenParen, 1:1); (Lex.CloseParen, 1:2); (Lex.OpenSquareBrkt, 1:4);
          (Lex.CloseSquareBrkt, 1:5); (Lex.OpenCurlyBrkt, 1:7);
          (Lex.CloseCurlyBrkt, 1:8); (Lex.OpenParen, 1:10);
          (Lex.OpenSquareBrkt, 1:12); (Lex.OpenCurlyBrkt, 1:14);
          (Lex.CloseParen, 1:16); (Lex.CloseSquareBrkt, 1:18);
          (Lex.CloseCurlyBrkt, 1:20)];
        end_pos = 1:21 }
    |}]

let%expect_test _ =
  lex ": . ," "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens = [(Lex.Colon, 1:1); (Lex.Dot, 1:3); (Lex.Comma, 1:5)];
        end_pos = 1:6 }
    |}]

let%expect_test _ =
  lex "foo # comment\nbar" "test.zt" |> show_lex_result |> print_endline;
  [%expect
    {|
      { Lex.tokens = [((Lex.Ident "foo"), 1:1); ((Lex.Ident "bar"), 2:1)];
        end_pos = 2:4 }
    |}]

let%test_unit _ =
  let f () = lex "$ " "test.zt" in
  assert_raises (UnexpectedChar ('$', { path = "test.zt"; col = 1; row = 1 })) f
