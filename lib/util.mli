val ( >> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
val uncurry2 : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
val get_or_else : 'a Option.t -> (unit -> 'a) -> 'a
