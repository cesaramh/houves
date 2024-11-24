(* term.mli *)
open Link;;

(* Strings in PI and LAMBDA constructors are only for printing *)
type tERM = 
            Type                            
          | KIND                            (* Constant KIND         *)
          | DB of int                       (* De Bruijn's indices   *)
          | Pi of string * tERM * tERM      (* Product type          *)
          | Lambda of string * tERM * tERM  (* Abstraction           *)
          | Metavar of string               (* Metavariable          *)
          | App    of tERM * tERM           (* Application           *)
          | Subs   of tERM * sUBS           (* Substitution          *)

and  sUBS = Shift of int                       (* Arrow                 *)
          | Cons of string * tERM * tERM* sUBS (* Constructor           *)
          | Comp of sUBS * sUBS                (* Composition           *)

;;

type context = sUBS

and constraint0 =  Meta of bool * context * string * tERM 
                   (* (habitation?) Ctx |- Metavar(nm):A *)
                | Eq of context * tERM * tERM 
                   (* Ctx |- M = Ctx |- N *)
                | Assign of context * string * tERM * tERM 
                   (* Ctx |- Metavar(nm) := M2 : A *) 
;;

type signature = constraint0 linkedList;;

val reduce: (tERM -> (bool * tERM)) list -> tERM -> tERM;;
val sys_beta: (tERM -> (bool * tERM)) list;;
val sys_sigma: (tERM -> (bool * tERM)) list;;
val sys_eta: (tERM -> (bool * tERM)) list;;
val sys_all: (tERM -> (bool * tERM)) list;;
val eq_term: tERM -> tERM -> bool;;
val eq_subs: sUBS -> sUBS -> bool;;
val fEq: constraint0 -> bool;;
val equiv_term: (tERM -> (bool * tERM)) list -> tERM -> tERM -> bool;;
val head_tail:tERM -> tERM * tERM list;;
val aPP:tERM -> tERM list -> tERM;;
val fun_Metavar: string -> tERM -> tERM -> (bool*tERM);;
val lemma_name: string -> string;;
val piGrade:tERM ->int;;
val isPure:tERM ->bool;;
val reduce_eq_types: signature -> context -> tERM -> tERM -> unit;;
val size_subs:sUBS->(int*int);;
val lf: string -> tERM -> context -> context;;
val push: string -> tERM -> tERM -> context -> context -> int -> context;;
val name2db: string -> string list -> int;;
val db2varType:int -> context ->tERM;;
val int2db:int -> string list -> tERM;;
val get_metavar: string -> signature -> constraint0;;
val get_sys:signature -> (tERM -> bool*tERM) list;;
val is_var: context -> string -> bool;;
val is_metavar: signature -> string -> bool;;
val inference_type: signature -> context -> tERM -> tERM;;
val inference_type_cons: signature -> signature -> context -> tERM -> tERM;;
val inference_type_subs: signature -> signature -> context -> sUBS -> context;;
val fun_eq_metavar: string -> constraint0 -> bool;;
val is_name_metavar: string -> constraint0 -> bool;;
val gen_var:string -> context -> string;;
val gen_metavar:string -> signature -> string;;
val reduce_all: signature -> tERM -> tERM;;
val go_metavar:string -> signature -> unit;;
val last_db:context -> int;;
val fun_isEq: constraint0 -> bool;;
val fun_isMetavar:constraint0 -> bool;;
val fun_isMetavarToSolve:constraint0 -> bool;;
val reduce_sig:signature -> signature;;
val cook:int -> tERM -> tERM;;
val unfoldl_app: tERM -> tERM list -> tERM;;
val get_var_names: context -> string list;;

exception ConversionError;;
exception UnTyped;;

