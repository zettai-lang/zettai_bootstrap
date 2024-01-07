let ( >> ) f g x = g (f x)
let get_or_else o f = match o with Some o -> o | None -> f ()
let char_quoted c = "'" ^ Char.escaped c ^ "'"
let quoted s = "\"" ^ String.escaped s ^ "\""
