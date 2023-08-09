let usage = Sys.argv.(0) ^ " [-debug] <FILE> [<ARGS>...]"
let debug = ref false
let file_opt = ref None
let args = ref []

let positional_fun arg =
  match !file_opt with
  | None -> file_opt := Some arg
  | Some _ -> args := !args @ [ arg ]

let speclist =
  [
    ("-debug", Arg.Set debug, "Output debug information");
    ("--", Arg.Rest positional_fun, "");
  ]

let () = Arg.parse speclist positional_fun usage

let file =
  match !file_opt with
  | Some f -> f
  | None ->
      Arg.usage speclist usage;
      exit 2

let () = Zettai_bootstrap.Exec.exec file
