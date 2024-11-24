(* Linked list *)
type 'a link = Nil  |
               Item  of 'a itemLink

and  'a itemLink = {val0:'a;
                    mutable next: 'a link;
                    mutable prev: 'a link}
;;

type 'a linkedList = {mutable head: 'a link;
                      mutable pos:  'a link;
                      mutable tail: 'a link;
                      mutable count:int}
;;

exception NIL_LINK;;
exception NoMapLink;;
val length_link : 'a linkedList -> int;;
val is_empty_link : 'a linkedList -> bool;;
val empty_link : unit -> 'a linkedList;;
val add_link : 'a linkedList -> 'a -> unit;;
val cons_link: 'a linkedList -> 'a -> unit;;
val ins_link: int -> 'a linkedList -> 'a -> unit;;
val remove_link : 'a linkedList -> unit;;
val remove_all_link:'a linkedList -> unit;;
val search_link: ('a -> bool) -> int -> int -> 'a linkedList -> unit;;
val exists_link: ('a -> bool) -> int -> int -> 'a linkedList -> 'a;;
val item_link : int -> 'a linkedList -> 'a;;
val go_head : 'a linkedList -> unit;;
val go_tail : 'a linkedList -> unit;;
val go_n: int -> 'a linkedList -> unit;;
val go_home:'a linkedList -> unit;;
val go_next : 'a linkedList -> unit;;
val go_prev : 'a linkedList -> unit;;
val append_link: 'a linkedList -> 'a linkedList -> unit;;
val intro_link: 'a linkedList -> 'a linkedList -> unit;;
val copy_link: 'a linkedList -> 'a linkedList;;
val filter_link: ('a -> bool) -> 'a linkedList -> 'a linkedList;;
val map_link: ('a -> 'b) -> 'a linkedList -> 'b linkedList;; 
val map_list_link: ('a -> 'b) -> 'a list -> 'b linkedList;;
val map_link_list: ('a -> 'b) -> 'a linkedList -> 'b list;;
val list2link: 'a list -> 'a linkedList;;
val link2list: 'a linkedList -> 'a list;;
val print_link: ('a -> bool -> unit) -> string -> string -> string 
                    -> string -> bool -> 'a linkedList -> unit;;
val cons_link_sorted: 'a -> ('a -> 'a -> bool) -> 'a linkedList -> unit;;
val add_link_sorted: 'a -> ('a -> 'a -> bool) -> 'a linkedList -> unit;;
