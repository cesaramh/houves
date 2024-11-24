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

let update_ctx () =
    cOOK := -1;
    if gOAL.pos <> Nil then
      match item_link 0 gOAL with
        Meta(_,ctx,_,_) -> cTX := ctx
      | Assign(ctx,_,_,_)-> cTX := ctx
      | _ -> ()
;;

let comm_check t = 
  try ( let sig1 = empty_link () in
        let k = inference_type_cons gOAL sig1 !cTX t in
        print_sig true sig1;
        print_jud (get_var_names !cTX) t k )
  with _ -> comm_error "" 5
;;

let comm_check_s s = 
  try (let sig1 = empty_link () in
       let d = inference_type_subs gOAL sig1 !cTX s in
       print_sig true sig1;
       print_jud_s (get_var_names !cTX) s d)
  with _ ->   
    comm_error "" 5 
;;

let comm_set_ctx s = 
  try (let sig1 = empty_link () in
       let d = inference_type_subs gOAL sig1 !cTX s in
       print_sig true sig1;
       print_jud_s (get_var_names !cTX) s d;
       cTX := d;
       cOOK := -1)
  with _ ->   
    comm_error "" 5 
;;

let comm_var nm t = 
   try
   ( let k = inference_type gOAL !cTX t in
     let t' = reduce_all gOAL t in
     if k = Type or k=KIND then
      ( if !cOOK >= 0 then cOOK := !cOOK+1;
       cTX := lf nm t' !cTX)
     else comm_error nm 4    
   ) with _ -> comm_error nm 4
;;

let comm_let nm t = 
  if is_var !cTX nm then
    comm_error nm 19
  else 
   try ( let k = reduce_all gOAL (inference_type gOAL !cTX t) in
         let k' = reduce_all gOAL (inference_type gOAL !cTX k) in
         if k'=Type or k'=KIND then (
           if !cOOK >= 0 then cOOK := !cOOK+1;
           cTX := push nm t k !cTX !cTX 0
         )
         else comm_error nm 4    
       )
   with _ -> comm_error nm 20
;;

let comm_metavar b n t =
  let nm = if b then n^"?"
           else n^"!" in
  if is_metavar gOAL nm then
    comm_error nm 7
  else 
  try (
    let k = if t=KIND then KIND else inference_type gOAL !cTX t in
    let t' = reduce_all gOAL t in
    if k = Type or k = KIND then 
    ( if gOAL.pos = Nil then
        cons_link gOAL (Meta(b,!cTX,nm,t'))
      else
        ins_link 0 gOAL (Meta(b,!cTX,nm,t'));
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
    else print_ctx2 !cTX
  );
  print_newline()
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
            cTX := ctx;
            (*********** OJOOOOOOOOOOOOOOOOOOOOOOOOO add substitution *)
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

let sys_eval = function
   0 -> sys_all
 | 1 -> sys_beta@sys_sigma
 | 2 -> sys_eta@sys_sigma
 | _ -> sys_sigma
;;

let comm_eval n t =
  try ( let k = inference_type gOAL !cTX t in
        let t' = reduce (get_sys gOAL@sys_eval n) (Subs(t,!cTX)) in
        print_term (get_var_names !cTX) t;
        print_string " = ";
        print_term (get_var_names !cTX) t';
        print_string " in the actual context.";
        print_newline())
  with _ ->   
    comm_error "" 5
;;

let rec main_loop inter ch =
try
    let lexbuf = Lexing.from_channel ch in
    while true do
         if inter then (print_prompt gOAL;line := 1);
         str_ctx := get_var_names !cTX;
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
          | Action(4) -> cTX := Shift(0); cOOK := -1
          | Action(5) -> remove_all_link gOAL;cOOK := -1
	  | Action(6) -> cTX := Shift(0); remove_all_link gOAL;cOOK := -1
	  | Cook(n) -> cOOK := n
          | Check t    -> comm_check (cook !cOOK t)
          | CheckS s    -> comm_check_s s
          | SetCtx s    -> comm_set_ctx s
          | Goals -> print_sig true gOAL
          | Var(nm,t) -> comm_var nm (cook !cOOK t)
          | Let(nm,t) -> comm_let nm (cook !cOOK t)
          | Go(n) -> comm_go n; comm_show inter
          | GoName(n) -> comm_goname n; comm_show inter
          | Ungoal -> comm_ungoal ()
          | MetaDecl(b,nm,t) -> comm_metavar b nm (cook !cOOK t); 
                                comm_show inter
          | Load(f) -> comm_load f
          | Save(nm) -> comm_save nm
          | Eval(n,t) -> comm_eval n (cook !cOOK t)
	  | Limit(i) -> comm_limit i
          | _        -> ()
         );
         if inter then print_newline ()
         with ErrorMsg -> ());
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
