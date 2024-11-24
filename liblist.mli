(* Yet another List Library *)

val pos_list: int -> int -> 'a list -> 'a;;
val search_list: int -> ('a -> bool) -> 'a list -> int;; 
val get_list:('a -> bool) -> 'a list -> 'a;;
val elim_list:('a -> bool) -> 'a list -> 'a list;;
val search_elim_list: ('a -> bool) -> 'a list -> 'a * 'a list;;
val print_list:('a -> unit)-> string -> string 
                  -> string -> string -> 'a list -> unit;;
val merge_list: 'a list -> 'b list -> ('a*'b) list;;
val fmerge_list: ('a->'c) ->('b->'d) -> 'a list -> 'b list -> ('c*'d) list;;
val insert_sorted: 'a -> ('a -> 'a -> bool) -> 'a list -> 'a list;;
val cut_list: int -> int -> 'a list -> 'a list;;
exception SearchList;;
exception NoMapList;;
