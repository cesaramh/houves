(* Yet another List Library *)

open List;;
exception SearchList;;
exception NoMapList;;

let pos_list m pos l = try nth l (pos-m) with _ -> raise SearchList
;;

let rec cut_list m l =
  if m < 0 or l=[] then []
  else if m = 0 then l 
  else cut_list (m-1) (tl l)
;; 

let rec search_list n fun_eq = function
  [] -> raise SearchList
| x::r -> if fun_eq x then n
          else search_list (n+1) fun_eq r
;;

let rec get_list fun_eq = function
  [] -> raise (SearchList)
| x::r -> if fun_eq x then x
          else get_list fun_eq r
;;

let rec elim_list fun_eq = function
  [] -> []
| x::r -> if fun_eq x then r
          else x::elim_list fun_eq r
;;

let search_elim_list fun_eq l = 
let rec search_elim_i li = function
  []   -> raise (SearchList)
| x::r -> if fun_eq x then (x,li@r)
          else search_elim_i (li@[x]) r in
  search_elim_i [] l
;; 

let rec print_list print_e empty se pi pd = function 
      [] -> print_string empty
    | x::y -> print_string pi;
              print_e x; 
              if y <> [] then (
                print_string se; 
                print_list print_e empty se "" "" y);
              print_string pd;;

let rec merge_list = fun
 p0 p1 -> match (p0,p1) with ((x::y), (z::w)) -> (x,z)::merge_list y w
| (_, _) -> []
;;

let rec fmerge_list f g = fun
 p0 p1 -> match (p0,p1) with ((x::y), (z::w)) -> (f x, g z)::fmerge_list f g y w
| (_, _) -> []
;; 

let rec insert_sorted a f = function
    [] -> [a]
  | (x::y) as l -> 
      if f a x then a::l
      else x::insert_sorted a f y
;;







