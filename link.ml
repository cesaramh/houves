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

(* value new_item : 'a -> 'a Link *)
let new_item a = Item({val0 = a;next=Nil;prev=Nil})
;;

(* value set_next : 'a Link -> 'a Link -> unit *)
let set_next item p = match item with
  Nil -> ()
| Item(i) -> i.next <- p;()
;;

(* value set_prev : 'a Link -> 'a Link -> unit *)
let set_prev item p = match item with
  Nil -> ()
| Item(i) -> i.prev <- p;()
;;

(* value get_next : 'a Link -> 'a Link *)
let get_next item = match item with
  Nil -> Nil
| Item(i) -> i.next
;;

(* value get_val : 'a Link -> 'a *)
let get_val item = match item with
  Nil -> raise NIL_LINK
| Item(i) -> i.val0
;;

(* value get_prev : 'a Link -> 'a Link *)
let get_prev item = match item with
  Nil -> Nil
| Item(i) -> i.prev
;;

(* value ins_after : 'a Link -> 'a Link -> unit *)
let ins_after pos i = 
   let next = get_next pos in
   set_next pos i;
   set_next i next;
   set_prev next i;
   set_prev i pos
;;

(* value empty_link : unit -> 'a LinkedList *)
let empty_link () = {head=Nil;
                     tail=Nil;
                     pos=Nil;
                     count=0}
;;

(* value length_link : 'a LinkedList -> int *)
let length_link l = l.count
;;

(* value is_empty_link : 'a LinkedList -> bool *)
let is_empty_link l = (l.count = 0)
;;

(* value go_head : 'a LinkedList -> unit *)
let go_head l = (l.pos <- l.head)
;;

(* value go_tail : 'a LinkedList -> unit *)
let go_tail l = (l.pos <- l.tail)
;;

(* value go_next : 'a LinkedList -> unit *)
let go_next l = 
  if is_empty_link l then ()
  else if l.pos = Nil then go_head l
  else (l.pos <- get_next (l.pos))
;;

(* value go_prev : 'a LinkedList -> unit *)
let go_prev l = 
  if is_empty_link l then ()
  else if l.pos = Nil then go_tail l
  else(l.pos <- get_prev (l.pos))
;;


(* value go_home : 'a LinkedList -> unit *)
let go_home l =
  go_head l;
  go_prev l
;;

let next_p b = 
  if b then get_next else get_prev
;;

let next_n b = 
  if b then pred else succ
;;

let go_i pos n =
let rec go_iter pos n nextp nextn =
   if (pos = Nil or n=0) then pos
   else go_iter (nextp pos) (nextn n) nextp nextn

in let b = n>0 in 
   let nextp = next_p b in
   let nextn = next_n b in
   go_iter pos n nextp nextn
;;

(* value go_n : int -> 'a LinkedList -> unit 
   n > 0  -> next, n < 0 -> prev  *)
let go_n n l =
   if is_empty_link l then ()
   else if l.pos = Nil & n>0 then 
   (  go_head l;
      l.pos <- go_i l.pos (n-1) )  
   else if l.pos = Nil & n<0 then 
   (  go_tail l;
      l.pos <- go_i l.pos (n+1) )  
   else 
      l.pos <- go_i l.pos n 
;; 

(* value item_link: int -> 'a LinkedList -> 'a *)
let item_link n l = 
   get_val (go_i l.pos n)
;;

let search_item f w n l=
let rec search_iter p next = 
    if p = Nil then p
    else if f (get_val p) then p
    else search_iter (next p) next
in 
   let nextp = 
     if (w > 0) then next_p true 
     else if (w < 0) then next_p false
     else if (n>0) then next_p true
     else if (n<0) then next_p false 
     else (fun x -> Nil)
   in
   let pos = 
     if (w <> 0) then (go_i l.pos n)
     else if (n>0) then l.head
     else if (n<0) then l.tail
     else l.pos
   in
   search_iter pos nextp  
;;

(* For search and exist:
   w>0  -> search to next of (actual position+n) (n maybe negative)
   w<0  -> search to prev of (actual position+n) (n maybe negative)
   w=0  n=0 -> search only at actual position
   w=0  n>0 -> search to the next of the head
   w=0  n<0 -> search to the prev of the tail *)
 
(* value search_link:  ('a -> bool) -> int -> int -> 'a LinkedList -> unit *)
let search_link f w n l =
   l.pos <- search_item f w n l
;;    

(* value exists_link:  ('a -> bool) -> int -> int -> 'a LinkedList -> 'a *)
let exists_link f w n l =
   get_val (search_item f w n l)
;;    

(* value cons_link : 'a LinkedList -> 'a -> unit *)
let cons_link l a = 
  let i = new_item a in
  if is_empty_link l then
    l.tail <- i;
  set_next i l.head;
  set_prev l.head i;
  l.pos <- i;
  l.head <- i;
  l.count <- l.count + 1
;;

(*value remove_pos : 'a Link -> unit *)
let remove_pos pos =
   let next = get_next pos in
   let prev = get_prev pos in
   set_next prev next;
   set_prev next prev
;;

(* value remove_link : 'a LinkedList -> unit *)
let remove_link l =
  if l.pos = Nil then ()
  else 
  ( if l.pos = l.head then
      l.head <- get_next l.pos
    else if l.pos = l.tail then
      l.tail <- get_prev l.tail;
    remove_pos l.pos;
    l.count <- l.count -1;
    if l.count = 0 then (
      l.pos <- Nil;
      l.head <- Nil;
      l.tail <- Nil
    ) else 
      l.pos <- get_prev(l.pos);
  )
;;
  
(* value remove_all_link:'a LinkedList -> unit *)
let remove_all_link l=
  go_tail l;
  while (not (is_empty_link l)) do
    remove_link l; 
  done
;;
 
(* value add_link : 'a LinkedList -> 'a -> unit *)
let add_link l a = 
  let i = new_item a in
  if is_empty_link l then
   l.head <- i;
  set_next l.tail i;
  set_prev i l.tail;
  l.pos <- i;
  l.tail <-i;
  l.count <- l.count + 1
;;

(* value ins_link : int -> 'a LinkedList -> 'a -> unit *)
let ins_link n l a =
  let pos = go_i l.pos n in
  if pos = Nil then (if n >0 then add_link l a else cons_link l a)
  else if pos = l.tail then 
    add_link l a
  else
  let i = new_item a in
  ( ins_after pos i;
    l.pos <- i;
    l.count <- l.count + 1)
;;

(* value print_link :
   ('a -> bool -> unit)-> string -> string -> string -> string -> bool
   -> 'a LinkedList -> unit.
*)

let print_link print empty spa left right b l =
  let rec print_item i next c = 
    ( if (c=0) then ()
      else if (i=l.pos) then
        print (get_val i) true
      else print (get_val i) false;
      let p = next i in
      if (c <> 1) then 
      ( print_string spa;
        print_item p next (c-1)) )
  in
  if is_empty_link l then print_string empty
  else
  ( print_string left;
    print_item (if b then l.head else l.tail) (next_p b) (l.count);
    print_string right);
  flush stdout
;;

let append_link l1 l2 =
  if is_empty_link l2 then ()
  else 
    (if is_empty_link l1 then
       l1.head <- l2.head
     else
     ( set_next (l1.tail) (l2.head);
       set_prev (l2.head) (l1.tail));
     l1.tail <- l2.tail;
     l1.count <- l1.count + l2.count)
;;

let intro_link l1 l2 =
  if is_empty_link l1 or is_empty_link l2 then append_link l1 l2
  else if l1.pos = Nil then (
    set_next (l2.tail) (l1.head);
    set_prev (l1.head) (l2.tail);
    l1.head <- l2.head;
    l1.count <- l1.count + l2.count
  )
  else 
    let next = get_next l1.pos in
    if next = Nil then append_link l1 l2
    else
    ( set_next l1.pos l2.head;
      set_prev l2.head l1.pos;
      set_next l2.tail next;
      set_prev next l2.tail;
      l1.count <- l1.count + l2.count )
;;

let copy_link l1 =
  let pos = l1.pos in
  go_tail l1;
  let l2 = empty_link () in
  while l1.pos <> Nil do
    cons_link l2 (item_link 0 l1); 
    go_prev l1
  done;
  go_tail l1;
  go_tail l2;
  while (l1.pos <> pos & l1.pos <> Nil) do
    go_prev l1;
    go_prev l2;
  done;
  l2
;;

let cons_link_sorted a f l =
  go_head l;
  while (l.pos <> Nil) & (f (item_link 0 l) a ) do
    go_next l;
  done;
  if (l.pos == Nil) then
    add_link l a
  else ins_link (-1) l a
;;

let add_link_sorted a f l =
  go_tail l;
  while (l.pos <> Nil) & (f a (item_link 0 l)) do
    go_prev l;
  done;
  if (l.pos == Nil) then
    cons_link l a
  else ins_link 0 l a
;;

let filter_link f l =
  let lold = l.pos in 
    go_head l;
    while l.pos <> Nil do
      if f (item_link 0 l) then remove_link l;
      go_next l;
    done;
    l.pos <- lold;
    l
;;

let map_list_link f l =
  let rec map_i l' = function
    [] -> go_head l';l'
  | x::y -> try
              let ni = (f x) in
              add_link l' ni;
              map_i l' y
            with NoMapLink -> map_i l' y 
  in
  let l' = empty_link () in
  map_i l' l
;;

let map_link f l =
  let rec map_link_i l' =
    if l.pos = Nil then ()
    else 
     try 
      let ni = f (item_link 0 l) in
        go_next l;
        add_link l' ni;
        map_link_i l'
     with NoMapLink -> go_next l;
                       map_link_i l'
  in
  let l' = empty_link() in
  if is_empty_link l then
    l'
  else (
    let pos = l.pos in
      if pos = Nil then
        go_head l;
      map_link_i l';
      l.pos <- pos;
      go_head l';
      l'
  )
;;

let map_link_list f l =
  let rec map_link_i l' =
    if l.pos = Nil then l'
    else 
     try 
      let ni = f (item_link 0 l) in
        go_next l;
        map_link_i (l'@[ni])
      with NoMapLink -> go_next l;
                        map_link_i l'
  in
    let pos = l.pos in
      if pos = Nil then
        go_head l;
      let l' = map_link_i [] in
      l.pos <- pos;l'
;;

let list2link l =
  map_list_link (fun x->x) l
;;

let link2list l =
  map_link_list (fun x->x) l
;;
