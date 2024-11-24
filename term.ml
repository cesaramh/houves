(* term.ml *)

open Link;;
open List;;
open Liblist;;
exception ConversionError;;
exception UnTyped;;

type tERM = 
            Type                            
          | KIND                            (* Constant KIND         *)
          | DB of int                       (* De Bruijn indices     *)
          | Pi of string * tERM * tERM      (* Product type          *)
          | Lambda of string * tERM * tERM  (* Abstraction           *)
          | Metavar of string               (* Metavariable          *)
          | App    of tERM * tERM           (* Application           *)
          | Subs   of tERM * sUBS           (* Substitution          *)
          | TypeConst of string*tERM*tERM   (* Constant nm:=term:type*)
          | Const of int*tERM               (* Constant db:=term     *)
          | Begin                           (* Marks begin of section*)
          | End                             (* Marks end of section  *)

and  sUBS = Shift of int                  (* Arrow                 *)
          | Cons of tERM * tERM * sUBS    (* Constructor           *)
          | Comp of sUBS * sUBS           (* Composition           *)

;;

type contextName = string list 

and context = {mutable localTerm : tERM list; (* Used to improve HOU *) 
               mutable globalTerm : tERM list;
               mutable local : int;
               mutable global : int;
               mutable listName : contextName}

and constraint0 =  Meta of bool * context * string * tERM 
                   (* (habitation?) Ctx |- Metavar(nm):A *)
                | Eq of contextName * contextName * tERM * tERM 
                   (* Ctx1 |- M = Ctx2 |- N *)
                | Assign of context * string * tERM * tERM 
                   (* Ctx |- Metavar(nm) := M2 : A*) 
;;

type signature = constraint0 linkedList;;

let sYMV = ref(-1);;
let sYMG = ref(-1);;

let gen_sym var =
  let sYM = if var then (sYMV := !sYMV + 1;!sYMV)
            else (sYMG := !sYMG + 1;!sYMG) in
  let nm = if var then "v" else "#" in
  let ns = string_of_int sYM in
  if var then nm^ns else nm^ns^"?" 
;;

let rec gen_symbol nm var f =
  if (nm = "") or (f nm) then gen_symbol (gen_sym var) var f
  else nm
;;

let is_name_metavar x = function
    Meta(_,_,y,_) ->x=y
  | Assign(_,y,_,_) -> x=y
  | _ -> false
;;

let is_metavar sig0 nm = 
  try (let i=exists_link (is_name_metavar nm) 0 1 sig0 in true)
  with
    _ -> false;;

let gen_metavar nm sig0 =
  gen_symbol nm false (is_metavar sig0)
;;

let is_var ctx nm = 
  try let x = get_list (function x -> x=nm) ctx.listName in
      true 
  with
    _ -> false;;

let rec gen_var nm ctx =
  gen_symbol nm true (is_var ctx)
;;

let lemma_name nam = String.sub nam 0 ((String.length nam) - 1)
;;

(* Check for term equivalence. p0 and p1 are normal forms *)
let rec eq_term = fun
  p0 p1 -> match (p0,p1) with (Type, Type) -> true
| (DB(n),DB(m))    -> n=m
| ((TypeConst(nm1,_,_)), (TypeConst(nm2,_,_))) -> nm1 = nm2
| (Const(n,_),Const(m,_)) -> n=m
| ((Metavar x1), (Metavar x2)) -> x1 = x2  
| ((Pi(_,t1,t2)), (Pi(_,t1',t2'))) -> 
    (eq_term t1 t1') & (eq_term t2 t2')
| ((Lambda(_,t1,t2)), (Lambda(_,t1',t2'))) -> 
    (eq_term t1 t1') & (eq_term t2 t2')
| ((App(t1,t2)), (App(t1',t2'))) -> 
    (eq_term t1 t1') & (eq_term t2 t2')
| ((Subs(t,s)), (Subs(t',s'))) -> 
    (eq_term t t') & (eq_subs s s')
| (Begin,Begin) -> true
| (End,End) -> true
| (_, _)-> false

and eq_subs = fun p0 p1 -> match (p0,p1) with
  (Shift(n), Shift(m)) -> n=m
| ((Cons(a,t,s)), (Cons(a',t',s'))) -> 
    (eq_term a a') & (eq_subs s s')
| ((Comp(s1,s2)), (Comp(s1',s2'))) -> 
    (eq_subs s1 s1') & (eq_subs s2 s2')
| (_, _) -> false
;;

let fEq = function
  Eq(_,_,x,y) -> if eq_term x y then true else false
|  _ -> false;;
 
(* Explicit substitutions rewriting system *)

let rec reduction  t = function
      [] -> (false,t)
    | fun_reg::y -> let resp = fun_reg  t in
                    if (fst resp) then resp
                    else reduction  t y
;;

let rec reduction_sub  s sr_sub sr_ter = 
      let result = reduction  s sr_sub in
        match result with 
           (true,t) -> result
       |  (false,Cons(a1,t1,s1)) ->
            let a1' = reduction_ter  a1 sr_ter sr_sub in
            let t1' = reduction_ter  t1 sr_ter sr_sub in
            let s1' = reduction_sub  s1 sr_sub sr_ter in
            ((fst a1') or (fst t1') or (fst s1'),Cons(snd a1',snd t1',snd s1'))
        |  (false,Comp(s1,s2)) ->
            let s1' = reduction_sub  s1 sr_sub sr_ter in
            let s2' = reduction_sub  s2 sr_sub sr_ter in
            ((fst s1') or (fst s2'),Comp(snd s1',snd s2'))
       |  _ -> result

and  reduction_ter  t sr_ter sr_sub  = 
      let result = reduction  t sr_ter in
         match result with
           (true,t) -> result
         | (_, App(a1,a2)) ->
            let a1' = reduction_ter  a1 sr_ter sr_sub in
            let a2' = reduction_ter  a2 sr_ter sr_sub in
            ((fst a1') or (fst a2'),App(snd a1',snd a2'))
        |  (_,Pi(s,a1,a2)) -> 
            let a1' = reduction_ter  a1 sr_ter sr_sub in
            let a2' = reduction_ter  a2 sr_ter sr_sub in
            ((fst a1') or (fst a2'),Pi(s,snd a1',snd a2'))
        |  (_,Lambda(s,a1,a2)) -> 
            let a1' = reduction_ter  a1 sr_ter sr_sub in
            let a2' = reduction_ter  a2 sr_ter sr_sub in
            ((fst a1') or (fst a2'),Lambda(s,snd a1',snd a2'))
        |  (_,Subs(t,s))   -> 
            let t' = reduction_ter  t sr_ter sr_sub in
            let s' = reduction_sub  s sr_sub sr_ter in
            (fst t' or fst s',Subs(snd t',snd s'))
        |  _ -> result
;;

let rec sys_reduction_ter  t sr_ter sr_sub  =
    let (e,t') = reduction_ter  t sr_ter sr_sub  in
    if e then sys_reduction_ter  t' sr_ter sr_sub 
    else t'
;;

let rec sys_reduction_sub  s sr_sub sr_ter  =
    let (e,s') = reduction_sub  s sr_sub sr_ter  in
    if e then sys_reduction_sub  s' sr_sub sr_ter 
    else s'
;;

(* Rules *)
let fun_Beta  = function 
  App(Lambda(_,a,x),y) -> (true,Subs(x,Cons(y,a,Shift(0))))
| x -> (false,x)
;;

let fun_Application  = function 
  Subs(App(x,y),z) -> (true,App(Subs(x,z),Subs(y,z)))
| x -> (false,x)
;;

let fun_Lambda  = function 
  Subs(Lambda(nom,a,x),y) -> 
    (true,Lambda(nom,Subs(a,y),Subs(x,Cons(DB(1),a,Comp(y,Shift(1))))))
| x -> (false,x)
;;

let fun_Pi  = function 
  Subs(Pi(nom,a,x),y) -> 
    (true,Pi(nom,Subs(a,y),Subs(x,Cons(DB(1),a,Comp(y,Shift(1))))))
| x -> (false,x)
;;

let fun_Clos  = function 
  Subs(Subs(x,y),z) -> (true,Subs(x,Comp(y,z)))
| x -> (false,x)
;;

let fun_VarCons  = function 
  Subs(DB(n),Cons(x,_,y)) -> if n>1 then (true,Subs(DB(n-1),y))
                             else (true,x) (* n = 1 *)
| x -> (false,x)
;;

let fun_Id  = function 
  Subs(x,Shift(0)) -> (true,x)
| x -> (false,x)
;;

let fun_Ass  = function 
  Comp(Comp(x,y),z) -> (true,Comp(x,Comp(y,z)))
| x -> (false,x)
;;

let fun_Map  = function 
  Comp(Cons(x,a,y),z) -> (true,Cons(Subs(x,z),a,Comp(y,z)))
| x -> (false,x)
;;

let fun_Idl  = function 
  Comp(Shift(0),x) -> (true,x)
| x -> (false,x)
;;

let fun_Idr  = function 
  Comp(x,Shift(0)) -> (true,x)
| x -> (false,x)
;;

let fun_ShiftCons  = function 
  Comp(Shift(n),Cons(x,a,y)) -> if n>0 then (true,Comp(Shift(n-1),y))
                                else (true,Cons(x,a,y)) (* n = 0 *)
| x -> (false,x)
;;

let fun_ShiftShift = function
  Comp(Shift(n),Shift(m)) -> (true,Shift(n+m))
| x -> (false,x)
;;

let fun_VarShift = function
  Subs(DB(n),Shift(m)) -> (true,DB(n+m))
| x -> (false,x)
;;

let fun_SCons  = function 
  (Cons(DB(n),_,Shift(m)) as a) -> if m = n then (true,Shift(n-1)) (* n > 0 *)
                                   else (false,a)
| x -> (false,x)
;;

let fun_Type  = function
  Subs(Type,s) -> (true,Type)
| x -> (false,x)
;;

let fun_Delta  = function
  Const(n,t) -> (true,t)
| x -> (false,x)
;;

(*-- Assume that the term is in sigma normal form --*)
let rec eta n = function
  App(x,y) -> App(eta n x,eta n y)
| Lambda(m,x,y) -> Lambda(m,eta n x,eta (n+1) y)
| (DB(m) as x) -> 
           if m = n then raise ConversionError 
           else if m < n then x
           else DB(m-1)
| (Subs(x,Shift(m))) as x0 -> 
               if (m >= n) then Subs(x,Shift(m-1))
               else if (m=n-1) then raise ConversionError
               else x0
| x -> raise ConversionError
;;

let fun_Eta = function
  (Lambda(_,_,App(x,DB(1)))) as x0 -> (try (true,eta 1 x) with _ -> (false,x0))
| x -> (false,x)
;;

let fun_Metavar nm t = function
  (Metavar(x)) as x0 -> if x = nm then (true,t)
                       else (false,x0)
| x -> (false,x)
;;

let sys_sigma = [fun_Id; fun_VarCons; fun_Clos; fun_Lambda; fun_Pi;
                fun_Application; fun_VarShift; fun_Type] 
;;

let sys_beta  = [fun_Beta]
;;

let sys_delta = [fun_Delta]
;;

let sys_eta = [fun_Eta]
;;

let sys_all = sys_beta @ sys_eta @ sys_delta @ sys_sigma
;;

let sys_subs = [fun_Ass; fun_Idl; fun_Idr; fun_ShiftCons; fun_ShiftShift; fun_Map;
                fun_SCons]
;;

let reduce sys t = sys_reduction_ter t sys sys_subs
;;
 
let equiv_term sys t1 t2 = eq_term (reduce sys t1) (reduce sys t2)
;;

(* The term (t) is in all normal form, the type (a) is sigma reduced *)
let lHNF t a =
  let rec application x = function
    0 -> x
  | n -> application (App(x,DB(n))) (n-1)
  in
  let rec lHNF_i n t = function
    Pi(u,v,w) -> (match t with 
                    Lambda(x,y,z) -> Lambda(x,y,lHNF_i n z w)
                  | x -> Lambda(u,v,lHNF_i (n+1) x w))
  | x -> let x0 = reduce sys_sigma (Subs(t,Shift(n))) in
         (application x0 n)
  in
  lHNF_i 0 t a 
;;

(* Pre: Terms are in all normal form *)
let rec aPP x = function
  [] -> x
| y::z -> App(x,aPP y z)
;;

(* Pre: Term is in normal form *)
let head_tail a =
  let rec head_tail_i l = function
    App(x,y) -> head_tail_i (y::l) x
  | x -> (x,l)
  in
  head_tail_i [] a
;;

let rec piGrade = function
    Pi(_,_,y) -> 1+piGrade y
  | _ -> 0
;;

(* The term does not contain meta-variables. PRE: It's in sigma normal form *)
let rec isPure = function
  Metavar(x) -> false
| Pi(_,x,y) -> (isPure x) & (isPure y)
| Lambda(_,x,y) -> (isPure x) & (isPure y)
| App(x,y) -> (isPure x) & (isPure y)
| Subs(_,_) -> false
| TypeConst(_,x,y) -> (isPure x) & (isPure y)
| Const(_,x) -> isPure x
| _ -> true 
;;

let rec size_subs = function
  Shift(n) -> (0,n)
| Cons(_,_,s) -> let (l,r) = size_subs s in
                   (l+1,r)
| _ -> (0,0)
;; 


let isPureCtx ctx = (fold_left (fun x y -> x & (isPure y)) true ctx.localTerm) &
                    (fold_left (fun x y -> x & (isPure y)) true ctx.globalTerm)
;;

let empty_ctx () = {globalTerm = [];localTerm = []; global = 0; local = 0; listName = []}
;;

let init_ctx ctx =
  ctx.globalTerm <- [];
  ctx.localTerm <- [];
  ctx.global <- 0;
  ctx.local <- 0;
  ctx.listName <- []
;;

let copy_ctx c = {
  globalTerm = c.globalTerm;
  localTerm = c.localTerm; 
  global = c.global; 
  local = c.local; 
  listName = c.listName
}
;; 

let var_decl_ctx nm t ctx = 
  {localTerm = t::ctx.localTerm;
   local = ctx.local + 1;
   globalTerm = ctx.globalTerm;
   global = ctx.global;
   listName = nm::ctx.listName
  }
;;

let add_local_var nm t ctx = 
  ctx.listName <- nm::ctx.listName;
  ctx.localTerm <- t::ctx.localTerm;
  ctx.local <- ctx.local + 1
;;

let add_global_var nm t ctx =
  if ctx.localTerm <> [] then raise ConversionError;
  ctx.listName <- nm::ctx.listName;
  ctx.globalTerm <- t::ctx.globalTerm;
  ctx.global <- ctx.global + 1
;;
  
let un_var ctx =
  if ctx.listName <> [] then 
    ctx.listName <- tl(ctx.listName);
  if ctx.localTerm <> [] then (
    ctx.localTerm <- tl(ctx.localTerm);
    ctx.local <- ctx.local -1
  ) else if ctx.globalTerm <> [] then (
    ctx.globalTerm <- tl(ctx.globalTerm);
    ctx.global <- ctx.global - 1
  ) else
    raise ConversionError
;;

let last_db ctx = ctx.local+ctx.global
;; 

let cut_vars n ctx = 
  if n > last_db ctx then raise ConversionError
  else if n <= ctx.local then 
    {localTerm = cut_list 1 n ctx.localTerm;
     local = ctx.local - n;
     globalTerm = ctx.globalTerm;
     global = ctx.global;
     listName = cut_list 1 n ctx.listName
   }
  else (* n <= last_db ctx *) 
    {globalTerm = cut_list (ctx.local+1) n ctx.globalTerm;
     global = (last_db ctx) - n;
     localTerm = [];
     local = 0;
     listName = cut_list 1 n ctx.listName
   }
;;

let get_vars ctx = ctx.localTerm@ctx.globalTerm
;;

let globalize_ctx ctx1 ctx2 = 
 ctx1.globalTerm <- get_vars ctx2;
 ctx1.localTerm <- [];
 ctx1.global <- last_db ctx2;
 ctx1.local <- 0;
 ctx1.listName <- ctx2.listName
;;

let int2DB n ctx = 
  if (n > last_db ctx) or (n <= 0) then raise ConversionError
  else DB(n)
;;

let name2db nm ctx =
  try search_list 1 (function x -> x=nm) ctx.listName with
  _ -> raise ConversionError
;;

let db2varType n ctx = 
  if (n > (last_db ctx)) or n <= 0 then raise SearchList
  else 
  let x = if n <= ctx.local then pos_list 1 n ctx.localTerm
          else pos_list (ctx.local+1) n ctx.globalTerm in
  if x = Begin or x=End then
    raise SearchList
  else x
;;

let fun_eq_metavar x = function
  Meta(_,_,y,_) ->x=y
| _ -> false
;;

let fun_isEq = function
  Eq(_,_,_,_) -> true
| _ -> false
;;

let fun_isMetavar = function
  Meta(_,_,_,_) -> true
| _ -> false
;;

let fun_isMetavarToSolve = function
  Meta(b,_,_,_) -> b
| _ -> false
;;

let go_metavar nm sig0 =
  try (
    search_link (fun_eq_metavar nm) 0 1 sig0;
  ) with _ -> raise UnTyped
      
;;

let is_assign_metavar x = function
    Assign(_,y,_,_) -> x=y
  | _ -> false
;;

let get_metavar nm sig0 =
    try 
     if (sig0.pos=Nil) then 
       (exists_link (is_name_metavar nm) 0 1 sig0) 
     else 
       try exists_link (is_assign_metavar nm) 0 0 sig0 
       with _ -> (exists_link (is_name_metavar nm) 1 1 sig0) 
    with _ -> raise UnTyped
;;

let get_sys sig0 =
  map_link_list (function Assign(_,x,p,_) -> fun_Metavar x p
                          |_ -> raise NoMapLink) sig0
;;

(* Reduce a context to its normal form *)
let reduce_ctx sys ctx =
  {localTerm = map (fun x -> reduce sys x) ctx.localTerm;
   globalTerm = map (fun x -> reduce sys x) ctx.globalTerm;
   global = ctx.global;
   local = ctx.local;
   listName = ctx.listName}
;;

let isLocalMetavar nm = (String.get nm 0) = '#'
;;

(* Reduce a signature to its normal form *)
let reduce_sig sig0 =
  if not (is_empty_link sig0) then (
    let main_sys = ref(sys_all) in 
    let sys = ref([]) in
    go_tail sig0;
    while sig0.pos <> Nil do
      let meta = item_link 0 sig0 in
      remove_link sig0;
      (match meta with
       Assign(ctx,nm,t,a) ->
          let the_sys = (!sys)@(!main_sys) in
          let new_t = reduce the_sys t in
          let new_fun = fun_Metavar nm new_t in
          if (!main_sys <> []) & (isLocalMetavar nm) then
            sys := new_fun :: !sys
          else (
            let new_meta = Assign(reduce_ctx the_sys ctx,nm,new_t,
                                  reduce the_sys a) in
            ins_link 0 sig0 new_meta;
            go_prev sig0;
            if (!main_sys <> []) then
              sys := new_fun :: !sys
          );
      | Meta(b,ctx,nm,a) ->
          main_sys := [];
          ins_link 0 sig0 (Meta(b,reduce_ctx !sys ctx, nm, reduce !sys a));
          go_prev sig0
      | Eq(ctx1,ctx2,t1,t2) ->
          main_sys := [];
          ins_link 0 sig0 (Eq(ctx1,ctx2,reduce !sys t1,reduce !sys t2));
          go_prev sig0
      );
    done
 );
 sig0
;;

let reduce_all sig0 t =
  let sys = get_sys sig0 in
  reduce (sys@sys_all) t
;;  

(* Pre: Types are in normal form. 
   Post: p11=p21,...,p1n=p2n if p1 and p2 are "compatibles",
         Conversion error if not.
*)

let rec reduce_eq_types sig0 ctx1 ctx2 = fun p0 p1 -> 
  if eq_term p0 p1 then ()
  else if (isPure p0) & (isPure p1) then
    raise UnTyped
  else 
(match (p0,p1) with 
  (Pi(n1,x1,y1), Pi(n2,x2,y2)) -> reduce_eq_types sig0 ctx1 ctx2 x1 x2;
                                  reduce_eq_types sig0 (n1::ctx1) (n2::ctx2)
                                                       y1 y2
| (x,y) -> 
   (match (head_tail x,head_tail y) with
     ((DB(n),l1),(DB(m),l2)) -> 
          if n = m then 
            (let sig'= filter_link fEq (map_list_link
                        (function (x0,y0) -> Eq(ctx1,ctx2,x0,y0)) 
                        (merge_list l1 l2)) in
             go_home sig0;
             intro_link sig0 sig')
          else raise UnTyped
    | _ -> cons_link sig0 (Eq(ctx1,ctx2,x,y))))
;;

let equiv_list_term sig0 sig1 lt1 lt2 = 
  let rec equiv_lt  = fun
    p0 p1 -> match (p0,p1) with 
    ([], []) -> ()
  | ((t1::r1), (t2::r2)) -> let t1f = reduce_all sig0 t1 in
                            let t2f = reduce_all sig0 t2 in
                            reduce_eq_types sig1  [] [] t1f t2f;
                            equiv_lt r1 r2
  | (_, _) -> raise UnTyped in

  if (lt1 = lt2) then ()
  else if (List.length lt1 = List.length lt2) then
    equiv_lt lt1 lt2
  else raise UnTyped
;;

let equiv_ctx sig0 sig1 ctx1 ctx2 =
  if (last_db ctx1) <> (last_db ctx2) then raise UnTyped;
  equiv_list_term sig0 sig1 (get_vars ctx1) (get_vars ctx2)
;;

let rec inference_type_term sig0 sig1 ctx = function 
  Type -> KIND
| DB(n) -> (try Subs(db2varType n ctx,Shift(n))
            with _-> raise UnTyped)
| Const(n,_) -> (try (match db2varType n ctx with
                       TypeConst(_,_,t) -> Subs(t,Shift(n))
                     | _ -> raise UnTyped)
                 with _-> raise UnTyped)
| Metavar nm -> (try (match get_metavar nm sig0 with
                        Meta(_,ctx',_,a) ->
                          equiv_ctx sig0 sig1 ctx' ctx;
                          a
                      | Assign(ctx',_,_,a) ->
                          equiv_ctx sig0 sig1 ctx' ctx;
                          a
                      |	_ -> (match get_metavar nm sig1 with
                        Meta(_,ctx',_,a) ->
                          equiv_ctx sig0 sig1 ctx' ctx;
                          a
                     | _ -> raise UnTyped))
                 with _ -> raise UnTyped)
| Subs(fo,s) -> let delta = inference_type_subs sig0 ctx s in
                let kf = inference_type_term sig0 sig1 delta fo in
                Subs(kf,s)
| Pi(_,a,b) -> let ctx' = var_decl_ctx "" a ctx in
               let t1 = inference_type_term sig0 sig1 ctx a in
               let t2 = inference_type_term sig0 sig1 ctx' b in  
               let ta= reduce_all sig0 t1 in
               if ta = Type or ta = KIND then
                 let rb = reduce_all sig0 t2 in
                 if rb = Type or rb = KIND then rb
                 else raise UnTyped
               else  raise UnTyped
| App(fo,m) ->  let t1 = inference_type_term sig0 sig1 ctx fo in
                let t1f = reduce_all sig0 t1 in 
                let t2= inference_type_term sig0 sig1 ctx m in
                let t2f = reduce_all sig0 t2 in
                (match t1f with
                  Pi(_,a,kf) -> 
                    reduce_eq_types sig1 ctx.listName ctx.listName a t2f;
                    Subs(kf,Cons(m,a,Shift(0)))
                | Metavar(_) 
                | Subs(Metavar(_),_) ->
                    let k = inference_type_term sig0 sig1 ctx t1f in
                    let kf = reduce_all sig0 k in
                    let new_K = gen_metavar "" sig0 in
                    let meta_K = Meta(true,var_decl_ctx "" t2f ctx,new_K,kf) in
                    cons_link sig1 meta_K;
                    cons_link sig1 (Eq(ctx.listName,ctx.listName,
                                       Pi("",t2f,Metavar(new_K)),t1f));
                    Subs(Metavar(new_K),Cons(m,t2f,Shift(0)))
                | _ -> raise UnTyped)
| Lambda(nom,a,m) -> let t1 = inference_type_term sig0 sig1 ctx a in
                     let ta = reduce_all sig0 t1
                     in
                     if ta=Type or ta=KIND then
                       let ctx' = var_decl_ctx nom a ctx in
                       let a' =  inference_type_term sig0 sig1 ctx' m in
                         Pi(nom,a,a')
                     else  raise UnTyped
| x -> raise UnTyped

and inference_type_subs sig0 ctx = function
  Shift(n) -> (try cut_vars n ctx with
               _ -> raise UnTyped)
| Cons(x,a,s) -> let ctx' = inference_type_subs sig0 ctx s in
                 var_decl_ctx "" a ctx'
| Comp(s,t) -> let delta' = inference_type_subs sig0 ctx t in
               let delta = inference_type_subs sig0 delta' s
               in delta
;;

(* Post Sig0, ctx |- term:(inference_type sig0 ctx term) or
        raise UnTyped if term is not well-typed,
        c contains a list of constraints that guarantee well-typedness of term
*)

let inference_type sig0 ctx term =
   let sig1 = empty_link () in 
   let t = inference_type_term sig0 sig1 ctx term in
   if is_empty_link sig1 then 
     reduce_all sig0 t
   else raise UnTyped
;;

let inference_type_cons sig0 sig1 ctx term =
  let t = inference_type_term sig0 sig1 ctx term in
     reduce_all sig0 t
;;

let discharge_local ctx =
  ctx.listName <- cut_list 1 ctx.local ctx.listName;
  ctx.local <- 0;
  ctx.localTerm <- []
;;  


let rec cook_t n = function
    Pi(s,x,y) -> Pi(s,cook_t n x, cook_t (n+1) y)
  | Lambda(s,x,y) -> Lambda(s,cook_t n x, cook_t (n+1) y)
  | Metavar(x) as a -> if n > 0 then Subs(Metavar(x),Shift(n)) else a
  | Subs(x,Shift(n)) as a -> if n>0 then Subs(cook_t n x,Shift(n)) else a
  | App(x,y) -> App(cook_t n x,cook_t n y)
  | x -> x
;; 

let cook n t = if n >= 0 then cook_t n t else t;;

let rec unfoldl_app t = function
    [] -> t
  | x::r -> unfoldl_app (App(t,x)) r
;; 
