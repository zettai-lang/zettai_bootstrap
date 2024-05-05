val ( >> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
val uncurry2 : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
val get_or_else : 'a option -> (unit -> 'a) -> 'a
val try_map : ('a -> 'b option) -> 'a list -> 'b list option
val try_fold_left : ('a -> 'b -> 'a option) -> 'a -> 'b list -> 'a option
