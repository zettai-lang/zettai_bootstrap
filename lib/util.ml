let ( >> ) f g x = g (f x)
let uncurry2 f (x, y) = f x y
let get_or_else o f = match o with Some o -> o | None -> f ()
