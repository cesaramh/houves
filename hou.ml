(* hou.ml *)
open Term;;
open Link;;
open Liblist;;
open Pp;;
open List;;
open Com;;

type sol =
  Sol of string*signature list 
             (* list of solutions for a metavariable            *)
| Any        (* No suggestions about the meta-variable to solve *)
;;

exception UnificationFailure;;
exception LimitExceeded;;
exception Solved;;

let instanciate p nm y = 
  let p' = empty_link () in 
  search_link (fun_eq_metavar nm) 0 1 p;
  match item_link 0 p with
    Meta(_,ctx,x0,a) ->
      cons_link p' (Assign(ctx,x0,y,a));
      Sol(nm,[p'])
  | _ -> raise UnificationFailure
;;

(* See definition of chi at page 90 of my thesis *)
let rec chi gamma m n = function
    0 -> (empty_link(),m,n)
  | i -> (let (new_Sigma,new_M,new_N) = chi gamma m n (i-1) in
            (match new_N with
             Pi(_,n1,n2) -> 
	      let new_metaName = gen_metavar "" new_Sigma in
	      let new_Meta = Meta(true,copy_ctx gamma, new_metaName,n1) in 
              let new_term = App(new_M,Metavar(new_metaName)) in
              let new_type = reduce sys_sigma 
                   (Subs(n2,Cons(Metavar(new_metaName),n1,Shift(0)))) in
	      cons_link new_Sigma new_Meta;
	      (new_Sigma,new_term,new_type)
             | _ -> (new_Sigma,new_M,new_N)))
;;

(* Imititate metavariable x with the term i *)
let apply_var p ctx x m i =
  try 
  let n = inference_type p ctx i in
  let k = piGrade n in
  let (ns,nm,nn) = chi ctx i n k in 
  let new_m = reduce_all p m in
  let new_nn = reduce_all p nn in
  reduce_eq_types ns ctx.listName ctx.listName new_m new_nn;
  cons_link ns (Assign(copy_ctx ctx,x,nm,new_m));
  ns with
  _ -> raise UnificationFailure
;;


(* When ctx |- x:(a:A)B in sig0, introduce a new metavariable a.ctx |- Y:B 
   and the assignement x:=[a:A]Y in sig0
*)
 
let intro_var sig0 ctx m x a b mv = 
  let new_x = gen_var x ctx in
  let ctx2 = var_decl_ctx new_x a ctx in
  let newm = Meta(true,ctx2,mv,b) in
  let t = Lambda(new_x,a,Metavar(mv)) in
  let new0 = Assign(ctx,m,t,Pi(x,a,b)) in
  ins_link 0 sig0 new0;
  ins_link 0 sig0 newm;
  go_n (-2) sig0;
;;

(* When ctx |- x:Kind, returns the assignement x:= Type in a new problem
*)

let assign_type ctx m a = 
  if a = KIND then (
    let p = empty_link() in
    let na = Assign(ctx,m,Type,KIND) in
    ins_link 0 p na;
    [p] )
  else 
    []
;;

(* When ctx |- x:a, a in {KIND,Type}, returns the problems
   [x:=(x:X).Y, Y:a, X:Type,
    x:=(x:X).Y, Y:a, X:Kind]
*)
 
let imitate_sort p ctx m a =
  let imitate_s na mY m1 s =
    let np = empty_link () in 
    let mX = Meta(true,ctx,m1,s) in
     ins_link 0 np na;
     ins_link 0 np mY;
     ins_link 0 np mX;
     np
  in
  if a = KIND or a = Type then 
    let m1 = gen_metavar "" p in
    let m2 = gen_metavar "" p in 
    let x = gen_var "" ctx in
    let xctx = var_decl_ctx x (Metavar(m1)) ctx in
    let t = Pi(x,Metavar(m1),Metavar(m2)) in
    let mY = Meta(true,xctx,m2,a) in
    let na = Assign(ctx,m,t,a) in
    [imitate_s na mY m1 KIND;imitate_s na mY m1 Type]
  else 
    []
;;

(* Counts the number of metavariables and equations of a signature.
   - m = unsolved metavariables
   - n = solved metavariables
   - e = equations
*)

let count_signature sig0 =
  let m = ref(0) in
  let e = ref(0) in 
  let n = ref(0) in
    go_head sig0;
    while sig0.pos <> Nil do
    (match item_link 0 sig0 with 
       Meta(b,_,_,_) -> if (b) then m:= !m+1
     | Eq(_,_,_,_) -> e:=!e+1
     | Assign(_,_,_,_)  -> n := !n+1
    );
    go_next sig0;
    done;
  (!m,!n,!e)
;;

(* pos_end <> 0 -> looking for begin of sec *)
let rec var_in_sections ls v_i_s n pos_end sec = function
  (_,[]) -> if pos_end <> 0 then
              cons_link v_i_s (n,pos_end)
| (nm::ln,Begin::lt) -> if pos_end <> 0 then 
                          if nm = ("Begin "^sec) then
                             (cons_link v_i_s (n,pos_end);
                              var_in_sections ls v_i_s (n+1) 0 "" (ln,lt))
                          else var_in_sections ls v_i_s (n+1) pos_end sec (ln,lt)
                        else (
                          try let _= search_list 1 (function x -> nm=("Begin "^x)) ls in
                              cons_link v_i_s (n,0);
                          with _ -> ();
                          var_in_sections ls v_i_s (n+1) pos_end sec (ln,lt);
                        )
| (nm::ln,End::lt) ->   if pos_end <> 0 then 
                          var_in_sections ls v_i_s (n+1) pos_end sec (ln,lt)
                        else (
                          try
                            let the_sec = get_list (function x -> nm=("End "^x)) ls in
                            var_in_sections ls v_i_s (n+1) n the_sec (ln,lt)
                          with
                            | _  -> var_in_sections ls v_i_s (n+1) pos_end sec (ln,lt) 
                        )
| (_::ln,_::lt) -> var_in_sections ls v_i_s (n+1) pos_end sec (ln,lt) 
| _ -> ()
;;
                          
let declared_in_sections v_i_s ls n =
  if ls = [] then true
  else (
    let sol = ref(-1) in
    go_head v_i_s;
    while (v_i_s.pos <> Nil) & (!sol < 0) do
      let (pos_begin,pos_end) = item_link 0 v_i_s in
      if n > pos_begin then sol := 0
      else if (n < pos_begin & n > pos_end) then sol := 1
      else go_next v_i_s
    done;
    if !sol <= 0 then false
    else true
  )
;;

(* Generate all the possible imitations for the ctx |- x:m in signature p in
   the list of sections ls.
   It takes in consideration the indices in ctx <= i and possibly h (if h >=0 ).
   It does not change p!
*)
let rec imitate_vis v_i_s ls p ctx x m h = function
    0 -> if h>0 & declared_in_sections v_i_s ls h then
           (try [apply_var p ctx x m (DB(h))] with
            UnificationFailure -> [])
         else []
  | i -> 
      if declared_in_sections v_i_s ls i then 
      (try 
         let ns = apply_var p ctx x m (DB(i)) in
           ns::(imitate_vis v_i_s ls p ctx x m h (i-1))
       with  
         UnificationFailure -> 
           imitate_vis v_i_s ls p ctx x m h (i-1)
      ) else imitate_vis v_i_s ls p ctx x m h (i-1)
;;

let imitate ls p ctx x m h =
   let v_i_s = empty_link () in
   if (ctx.local > 0) then 
     cons_link v_i_s (ctx.local+1,0);
   if (ls <> []) then
     var_in_sections ls v_i_s (ctx.local+1) 0 "" 
     (cut_list 1 ctx.local ctx.listName,ctx.globalTerm);
   imitate_vis v_i_s ls p ctx x m h
;;

let rec solve_meta ls p n h =
  match item_link 0 p with
    Meta(b,ctx,nm,t) ->
      (match reduce_all p t with
         Pi(x,a,b) ->
           let p' = empty_link () in
           let mv = gen_metavar "" p in
           intro_var p' ctx nm x a b mv;
           [p']
      | a -> if b then 
               let lp  =  (assign_type ctx nm a)@
                          (imitate ls p ctx nm a h 
                           (if h=0 & n=0 then last_db ctx else n)) @
		          (imitate_sort p ctx nm a) in
               lp
             else [])
 |  _ -> raise UnificationFailure
;;

(* Dealing with rigid=rigid, rigid-flex, flex-flex equations. 
   See decompose below. *)
let rigid_flex ls p ctx1 ctx2 x y = 
     match (head_tail x,head_tail y) with
       ((Metavar(nm),_::_),_) -> 
         ins_link 0 p (Eq(ctx1,ctx2,x,y));
	 go_metavar nm p;
         Sol(nm,solve_meta ls p 0 0)
     | (_,(Metavar(nm),_::_)) -> 
         ins_link 0 p (Eq(ctx1,ctx2,x,y));
	 go_metavar nm p;
         Sol(nm,solve_meta ls p 0 0)
     | ((Subs(Metavar(nm),_),_::_),_) -> 
         ins_link 0 p (Eq(ctx1,ctx2,x,y));
	 go_metavar nm p;
         Sol(nm,solve_meta ls p 0 0)
     | (_,(Subs(Metavar(nm),_),_::_)) -> 
         ins_link 0 p (Eq(ctx1,ctx2,x,y));
	 go_metavar nm p;
         Sol(nm,solve_meta ls p 0 0)
     | ((DB(n),l1),(DB(m),l2)) -> 
          if n = m then 
            (let sig'= filter_link fEq (map_list_link
                      (function (x0,y0) -> Eq(ctx1,ctx2,x0,y0)) 
                      (merge_list l1 l2)) in
             intro_link p sig';
             Any) 
          else raise UnificationFailure
     | ((DB(n),_),(Metavar(nm),[])) -> 
        ins_link 0 p (Eq(ctx1,ctx2,x,y));
        go_metavar nm p;
        Sol(nm,solve_meta ls p 0 n)
     | ((DB(n),_),(Subs(Metavar(nm),s),[])) -> 
          let (l,r) = size_subs s in
          let new_n = n-r+l in
          ins_link 0 p (Eq(ctx1,ctx2,x,y));
 	  go_metavar nm p;
          Sol(nm,solve_meta ls p l (if new_n <= l then 0 else new_n))
     | ((Metavar(nm),[]),(DB(n),_)) -> 
          ins_link 0 p (Eq(ctx1,ctx2,x,y));
  	  go_metavar nm p;
          Sol(nm,solve_meta ls p 0 n)
     | ((Subs(Metavar(nm),s),[]),(DB(n),_)) ->
          let (l,r) = size_subs s in
          let new_n = n-r+l in
          ins_link 0 p (Eq(ctx1,ctx2,x,y));
  	  go_metavar nm p;
          Sol(nm,solve_meta ls p l (if new_n <= l then 0 else new_n))
     | ((Metavar(nm),_),_) -> 
         ins_link 0 p (Eq(ctx1,ctx2,x,y));
	 go_metavar nm p;
         Sol(nm,solve_meta ls p 0 0)
     | ((Subs(Metavar(nm),_),_),_) -> 
         ins_link 0 p (Eq(ctx1,ctx2,x,y));
	 go_metavar nm p;
         Sol(nm,solve_meta ls p 0 0)
     | (_,(Metavar(nm),_)) -> 
         ins_link 0 p (Eq(ctx1,ctx2,x,y));
	 go_metavar nm p;
         Sol(nm,solve_meta ls p 0 0)
     | (_,(Subs(Metavar(nm),_),_)) -> 
         ins_link 0 p (Eq(ctx1,ctx2,x,y));
	 go_metavar nm p;
         Sol(nm,solve_meta ls p 0 0)
     | _ -> raise UnificationFailure
;;                      

(* Decompose an equality p0=p1 in [...,p0'=p1',...] 
   PRE: ls list of sections.
        p is the signature where p0=p1 appears.
        p0 and p1 are in normal form 
        (instantiate meta-variables are reduced).
   POST:The equation p0=p1 is erased from p.
        New equations are added to p.
        If the equation implies a list of solutions l, for a meta-variable nm, 
        then Sol(nm,l) is returned. Otherwise, the constant Any is returned.
        It raises UnificationFailure when an inconsistence is detected.
*)

let decompose ls p ctx1 ctx2 = fun
  t0 t1 -> remove_link p;
           let p0 = reduce_all p t0 in
           let p1 = reduce_all p t1 in
           if eq_term p0 p1 then Any
           else if (isPure p0) & (isPure p1) then
             raise UnificationFailure
           else 
( match (p0,p1) with
  (Metavar(m1), Metavar(m2)) -> 
    let p' = empty_link () in
    let first x0 = (fun_eq_metavar m1 x0) or (fun_eq_metavar m2 x0) in
    search_link first 0 1 p;
    (match item_link 0 p with
      Meta(b,ctx,x0,a) ->
        if x0 = m1 then (
          cons_link p' (Assign(ctx,x0,p1,a));
          Sol(m1,[p'])
        )
        else (
          cons_link p' (Assign(ctx,x0,p0,a));
          Sol(m2,[p'])
        )
     | _ -> raise UnificationFailure)
| (Pi(n1,x1,y1), Pi(n2,x2,y2)) ->
  ins_link 0 p (Eq(ctx1,ctx2,x1,x2));
  ins_link 0 p (Eq(n1::ctx1,n2::ctx2,y1,y2));
  Any
| (Lambda(n1,_,y1), Lambda(n2,_,y2)) ->
  ins_link 0 p (Eq(n1::ctx1,n2::ctx2,y1,y2));
  Any
| (Lambda(a,_,c),y) -> 
  ins_link 0 p (Eq(a::ctx1,a::ctx2,c,App(Subs(y,Shift(1)),DB(1))));
  Any
| (y,Lambda(a,_,c)) -> 
  ins_link 0 p (Eq(a::ctx1,a::ctx2,c,App(Subs(y,Shift(1)),DB(1))));
  Any
| ((Metavar(nm) as x), y) -> 
  if isPure y then instanciate p nm y
  else rigid_flex ls p ctx1 ctx2 x y
| (y,(Metavar(nm) as x)) ->  
  if isPure y then instanciate p nm y
  else rigid_flex ls p ctx1 ctx2 x y
| (x,y) -> rigid_flex ls p ctx1 ctx2 x y
)
;;

(* Expander: string list -> Signature -> Signatures 
   Pre:  p is the signature to solve.
         p.pos is a metava decl -- Meta(...), or an equation -- Eq(...)
         ls list of sections
   Post: Expands p with new equations. Returns Sol(nm,l) where l is a 
         list of solutions for
         nm, or Any if no suggestions are done.
         Raises UnificationFailure if an inconsistence is detected.
*)
let expander ls p = 
    let eq = item_link 0 p in
    match eq with
      Eq(ctx1,ctx2,t1,t2) ->
       decompose ls p ctx1 ctx2 t1 t2
    | Meta(_,_,nm,_) ->
       Sol(nm,solve_meta ls p 0 0)
    | _ -> raise UnificationFailure 
;;

(* First meta-variable or constraint to solve *)
let go_first_to_solve p =
  search_link fun_isEq 0 (-1) p;
  if (p.pos = Nil) then
    search_link fun_isMetavarToSolve 0 (-1) p
;;


let unsolved_grade o = match o with
  (m,n,e) -> (m*n)/(e+1)
;;

let order p1 p2 = (unsolved_grade (snd p1)) < (unsolved_grade (snd p2))
;;

let solved (m,n,e) = (m=0) & (e=0)
;;

let exceeded o = (unsolved_grade o) > !limit
;;

let rec create_newpbs pbs sig0 = function
  [] -> ()
| pn::r ->
    let new_sig = copy_link sig0 in
    intro_link new_sig pn;
    let new_grade = count_signature new_sig in
    if not (exceeded new_grade) then
      cons_link_sorted (new_sig,new_grade) order pbs;
    create_newpbs pbs sig0 r
;;

let print_pb = fun
 (sig0,(m,n,e)) b -> 
                 print_string "Unsolved: ";
                 print_int m;
                 print_string ", Solved: ";
                 print_int n;
                 print_string ", Equations: ";
                 print_int e;
                 print_string "\n";
                 print_sig false sig0
;;

let print_pbs pbs = print_string "List of problems:\n";
                    print_link print_pb "[##]\n" "=+=+=+=+=+=+=+=+=+=+=+=\n" 
                    "[#\n" "#]" 
                    true pbs
;; 

(* HOU: string list -> (signature,unsolved grade) linked_list -> unit.
   A signature is a problem: metavariables + constraints.
   Look for a solution only in sections listed in ls (everywhere if ls=[])
   The algorithm tries to solve one of the problems.
   Any problem with a unsolved grade larger that "limit" 
   (a global variable) is pruned.
   Three possible exceptions can be raised:
     - UnificationFailure 
     - LimitExceeded (all the unsolved problems exceed the limit)
     - Solved

*)

let hOU ls pbs =
  let initTime = Unix.time () in
  let next_stop = ref(-1) in
  let rounds = ref(0) in
  let newpbs = 
  try
    while true do
       if (not !verbose) & (!rounds mod 1000 = 0) then (
	 let t = (Unix.time() -. initTime) /. 60. in
         let st = if !rounds != 0 then 
                  ("("^(Printf.sprintf "%.2f min, " t)^
                    (string_of_int !rounds)^" rounds, "^
                    (string_of_int (length_link pbs))^" problems)") 
                  else "" in
         print_string ("Thinking ... "^st^"\n"); 
	 flush stdout 
       );
       rounds := !rounds +1;
       if (!next_stop = !rounds) then 
         verbose := true;
       if !verbose then (
         print_string "Round: ";
         print_int !rounds;
         print_newline();
         print_pbs pbs;
         print_newline();
         flush stdout
       );
       go_head pbs;
       if (is_empty_link pbs) then raise LimitExceeded;
       let (sig0,grade) = item_link 0 pbs in
       if solved grade then raise Solved
       else ( 
         remove_link pbs;
         go_first_to_solve sig0;
         if !verbose then (
           print_string "\nTo Solve:\n";
           print_sig true sig0;
           print_string 
           "\nRound ";
           print_int !rounds;
          print_string ". Next stop? <ENTER> = next round, n = round n, 0 = do not stop.\n";
           flush stdout;
           next_stop := (try int_of_string (read_line ()) with _ -> -1);
           if !next_stop >= 0 then (
              verbose := false; 
              print_string "Verbose OFF";
              if !next_stop > 0 then (
                print_string " until round ";
                print_int !next_stop
	      );
              print_newline();
              flush stdout
           )
         ); 
         try (
	   let newpbs = expander ls sig0 in
            (match newpbs with 
               Sol(_,[]) -> raise UnificationFailure
             | Sol(nm,l) -> 
                 search_link (fun_eq_metavar nm) 0 1 sig0;
                 remove_link sig0;
                 create_newpbs pbs sig0 l
             | Any -> let new_grade = count_signature sig0 in
                      if not (exceeded new_grade) then
                        cons_link_sorted (sig0,new_grade) order pbs)
         ) with UnificationFailure -> ()
       )
    done;
    empty_link()
  with    
    Solved ->  print_string "Unification succeeded. ";
               print_string "Use Goals or Save.\n";
               reduce_sig (fst (item_link 0 pbs))
  | LimitExceeded -> print_string 
     "Unification failed or unsolved problems exceed the limit.\n";
     print_string "Try with Limit n, where n > ";
     print_int !limit;
     print_string ".\n";
     empty_link()
  | _ -> print_string "Unfication failed.\n";
         empty_link()
  in 
  let t = (Unix.time() -. initTime) /. 60. in
  let st = Printf.sprintf "%.2f" t in 
  print_string ("Time: "^st^" min, Reminder problems: "^
                (string_of_int (length_link newpbs))^
                ", Rounds: "^(string_of_int !rounds)^".\n"); 
  newpbs
;;

let try_eq sig0 ctx t1 t2 = 
  let sig1 = empty_link () in
  let a1 = inference_type_cons sig0 sig1 ctx t1 in
  let a2 = inference_type_cons sig0 sig1 ctx t2 in
  reduce_eq_types sig1 ctx.listName ctx.listName a1 a2;
  cons_link sig1 (Eq(ctx.listName,ctx.listName,t1,t2));
  intro_link sig0 sig1
;;  

let try_term sig0 ctx t1 = 
  let sig1 = empty_link () in 
  let a1 = inference_type_cons sig0 sig1 ctx t1 in
  intro_link sig0 sig1
;;  

let unify l sig0 ctx t1 t2 = 
  try 
    try_eq sig0 ctx t1 t2;
    let pbs = empty_link () in
    cons_link pbs (copy_link sig0,count_signature sig0);
    let new_goal = hOU l pbs in
    if not (is_empty_link new_goal) then (
      remove_all_link sig0;
      append_link sig0 new_goal
    )
  with _ -> print_string "Unfication failed.\n";
;;  

