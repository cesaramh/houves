(* Author: Cesar Munoz (munoz@icase.edu)
   During the implementation I was associate to: INRIA, SRI and ICASE (now).
*)

open Term;;
open Com;;
open Par;;
open Lex;;
open Pp;;
open Link;;
open Liblist;;
open List;;
open Hou;;

let update_ctx () =
    cOOK := -1;
    if gOAL.pos <> Nil then
      match item_link 0 gOAL with
        Meta(_,ctx,_,_) -> globalize_ctx cTX ctx
      | Assign(ctx,_,_,_)-> globalize_ctx cTX ctx
      | _ -> ()
;;

let comm_check t = 
  try ( let sig1 = empty_link () in
        let k = inference_type_cons gOAL sig1 cTX t in
        print_sig true sig1;
        print_jud cTX.listName t k )
  with _ ->   
    comm_error "" 5
;;

let comm_var nm t = 
   try
   ( let k = inference_type gOAL cTX t in
     let t' = reduce_all gOAL t in
     if k = Type or k=KIND then
      ( if !cOOK >= 0 then cOOK := !cOOK+1;
        add_global_var nm t' cTX )
     else comm_error nm 4    
   ) with _ -> comm_error nm 4
;;

let comm_define nm t = 
  if is_var cTX nm then
    comm_error nm 19
  else 
   try ( let k = inference_type gOAL cTX t in
         if !cOOK >= 0 then cOOK := !cOOK+1;
         add_global_var nm (TypeConst(nm,t,k)) cTX )
   with _ -> comm_error nm 20
;;

let comm_metavar b n t =
  let nm = if b then n^"?"
           else n^"!" in
  if is_metavar gOAL nm then
    comm_error nm 7
  else 
  try (
    let k = if t=KIND then KIND else inference_type gOAL cTX t in
    let t' = reduce_all gOAL t in
    if k = Type or k = KIND then 
    ( if gOAL.pos = Nil then
        cons_link gOAL (Meta(b,copy_ctx cTX,nm,t'))
      else
        ins_link 0 gOAL (Meta(b,copy_ctx cTX,nm,t'));
      cOOK := 0;
      if (not b) then go_home gOAL
    ) 
    else comm_error nm 6;
  ) with _ -> comm_error nm 6 
;;

let comm_go n=
  if n = 0 then 
   go_home gOAL 
  else 
  ( go_n n gOAL;
    update_ctx()
  )
;;

let comm_goname nm =
  let pos = gOAL.pos in
  search_link (is_name_metavar nm) 0 1 gOAL;
  if gOAL.pos = Nil then
  (  gOAL.pos <- pos;
     comm_error nm 8
  ) else 
     update_ctx();
;;  

let comm_show inter =
  if (!cOOK <> -1) then
    print_string ("<<Cooking level: "^(string_of_int !cOOK)^">>\n");
  if inter then (
    if (not (is_empty_link gOAL)) & (not (gOAL.pos = Nil)) then
      print_constr2 (item_link 0 gOAL)
    else print_ctx2 cTX
  )
;;

let comm_unvar () =
  try (
   un_var cTX;
   if !cOOK >= 0 then cOOK := !cOOK-1
  )
  with _ -> comm_error "" 10
;;

let comm_ungoal() =
  if gOAL.pos = Nil then 
    comm_error "" 9
  else if gOAL.pos = gOAL.head then 
  (    remove_link gOAL;
       go_head gOAL;
       update_ctx()
  ) 
  else comm_error "" 13
;;

let comm_intro nm =
  if gOAL.pos = Nil then 
    comm_error "" 9
  else 
  (match item_link 0 gOAL with
     Meta(_,ctx,m,Pi(n,a,b)) ->
       ( let x = if (nm = "") & (n <> "") then n else gen_var nm ctx in
         let mv = gen_metavar "" gOAL in
         intro_var gOAL ctx m x a b mv;
         remove_link gOAL; 
         go_next gOAL;
         update_ctx() 
       )
     | _ -> comm_error "" 14
   ) 
;;

let comm_apply t =
  if gOAL.pos = Nil then 
    comm_error "" 9
  else 
  (match item_link 0 gOAL with
     Meta(_,_,nm,Pi(_,_,_)) -> comm_error "" 16
   | Meta(_,ctx,nm,a) ->
     (try  let ns = apply_var gOAL ctx nm a t in
           intro_link gOAL ns;
           remove_link gOAL;
           go_next gOAL
      with _ -> comm_error "" 16)
   | _ -> comm_error "" 16
  )
;;

let comm_save nm1 =
  if is_empty_link gOAL then 
    comm_error "" 18
  else ( 
      let pos = gOAL.pos in
      if pos = Nil then go_head gOAL;
      match item_link 0 gOAL with
        Assign(ctx,nm2,t,a) -> 
          if (* (isPureCtx ctx) & *) (isPure t) then (
            let nm = if nm1 <> "" then gen_var nm1 ctx 
                     else gen_var (lemma_name nm2) ctx in
            globalize_ctx cTX ctx;
            add_global_var nm (TypeConst(nm,t,a)) cTX;
            remove_all_link gOAL;
            cOOK := -1;
            comm_mssg 2 nm
          ) else (gOAL.pos <- pos;comm_error "" 17)
     | _ -> (gOAL.pos <- pos;comm_error "" 17)
  )
;;

let comm_limit i =
  Com.limit := i
;;

let rec all_sections ctx = function
  [] -> ()
| x::r -> if is_var ctx ("Begin "^x) then 
            all_sections ctx r
          else comm_error x 23;
;;

let comm_unify l t1 t2 =
  all_sections cTX l;
  unify l gOAL cTX t1 t2
;;

let comm_tryEq t1 t2 =
  try
    try_eq gOAL cTX t1 t2
  with _ -> comm_error "" 22
;;

let comm_try t1  =
  try
    try_term gOAL cTX t1 
  with _ -> comm_error "" 22
;;

let comm_resolve l =
  all_sections cTX l;
  let pbs = empty_link () in
  cons_link pbs (copy_link gOAL,count_signature gOAL);
  let new_goal = hOU l pbs in
  if not (is_empty_link new_goal) then (
    remove_all_link gOAL;
    append_link gOAL new_goal;
    cOOK := -1;
  )
;;

let sys_eval = function
   0 -> sys_all
 | 1 -> sys_beta@sys_sigma
 | 2 -> sys_delta@sys_sigma
 | 3 -> sys_eta@sys_sigma
 | _ -> sys_sigma
;;

let comm_eval n t =
  try ( let k = inference_type gOAL cTX t in
        let t' = reduce (get_sys gOAL@sys_eval n) t in
        print_term cTX.listName t;
        print_string " = ";
        print_term cTX.listName t';
        print_string " in the actual context.";
        print_newline())
  with _ ->   
    comm_error "" 5
;;

let comm_begin_sec nm =
  let bs = ("Begin "^nm) in
  if is_var cTX bs then
    comm_error nm 3;
  add_global_var bs Begin cTX
;;

let comm_end_sec nm  =
  let bs = ("Begin "^nm) in
  let es = ("End "^nm) in
  if not (is_var cTX bs) then
    comm_error nm 23;
  if is_var cTX es then
    comm_error nm 24; 
  add_global_var es End cTX
;;

let rec main_loop inter ch =
try
    let lexbuf = Lexing.from_channel ch in
    while true do
         if inter then (print_prompt gOAL;line := 1);
         let ctx = copy_ctx cTX in
         (try (match  (try  main token lexbuf with
                         Eof -> raise Eof 
                       | ConversionError -> 
                           comm_error (Lexing.lexeme lexbuf) 2;
                           Action(0)
                       | _   -> comm_error (Lexing.lexeme lexbuf) 1;
                                Action(0))
                       with 
            Action(0)  -> raise Eof              (* Quit  *)
          | Action(1)  -> print_help ()          (* Help  *) 
          | Action(2) -> verbose := not !verbose; (* Verbose *)
                         if !verbose then print_string "Verbose ON"
                         else print_string "Verbose OFF";
                         print_newline();
          | Action(3) -> comm_show true
          | Action(4) -> init_ctx cTX; cOOK := -1
          | Action(5) -> remove_all_link gOAL;cOOK := -1
	  | Action(6) -> init_ctx cTX;remove_all_link gOAL;cOOK := -1
	  | Cook(n) -> cOOK := n
          | Check t    -> comm_check (cook !cOOK t)
          | Goals -> print_sig true gOAL
          | Var(nm,t) -> comm_var nm (cook !cOOK t)
          | Go(n) -> comm_go n; comm_show inter
          | GoName(n) -> comm_goname n; comm_show inter
          | Unvar -> comm_unvar ()
          | Ungoal -> comm_ungoal ()
          | MetaDecl(b,nm,t) -> comm_metavar b nm (cook !cOOK t); 
                                comm_show inter
          | Load(f) -> comm_load f
          | Intro(nm) -> comm_intro nm; comm_show inter
          | Apply(t) -> comm_apply (cook !cOOK t); comm_show inter
          | Save(nm) -> comm_save nm
          | Define(nm,t) -> comm_define nm (cook !cOOK t)
          | Unify(l,t1,t2) -> comm_unify l (cook !cOOK t1) (cook !cOOK t2)
          | TryEq(t1,t2) -> comm_tryEq (cook !cOOK t1) (cook !cOOK t2)
          | Try(t1) -> comm_try (cook !cOOK t1)
          | Resolve(l) -> comm_resolve l
          | Eval(n,t) -> comm_eval n (cook !cOOK t)
	  | Limit(i) -> comm_limit i
          | BeginSec(nm) -> comm_begin_sec nm
          | EndSec(nm) -> comm_end_sec nm
          | _        -> ()
         );
         if inter then print_newline ()
         with ErrorMsg -> discharge_local cTX);
         (try (rglToEndOfLine tokenToEndOfLine lexbuf) with
            Eof -> raise Eof
          | _   -> ()) 
    done
with Eof -> ()

and

comm_load f =
  try 
    let ch = open_in f in
    print_string ("Loading: "^f);
    print_newline();
    let old_line = !line in
    line := 1;
    main_loop false ch;
    print_string (f^" has been loaded\n");
    line := old_line
  with Sys_error(e) -> (print_string e; print_newline ())
;;


(* Main *)
let _ = 
  print_welcome ();
  print_newline();
  main_loop true stdin;
  print_bye ()
;;
