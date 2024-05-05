let ( >> ) f g x = g (f x)
let uncurry2 f (x, y) = f x y
let get_or_else o f = match o with Some o -> o | None -> f ()

let rec try_map f = function
  | x :: xs ->
      Option.bind (f x) @@ fun y ->
      Option.bind (try_map f xs) @@ fun ys -> Some (y :: ys)
  | [] -> Some []

let rec try_fold_left f init : _ -> _ option = function
  | [] -> Some init
  | x :: xs -> Option.bind (f init x) @@ fun y -> try_fold_left f y xs
