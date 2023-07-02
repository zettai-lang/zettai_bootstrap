exception TODO

let exec_ast (_ast : Parse.ast) (_debug : bool) = raise TODO

let exec (path : string) (_args : string list) (debug : bool) =
  let text = Core.In_channel.read_lines path in
  let ast = String.concat "\n" text |> Parse.parse in
  exec_ast ast debug
