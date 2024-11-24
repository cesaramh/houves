(* hou.mli *)
open Term;;
open Link;;

val unify: string list -> signature -> context -> tERM -> tERM -> unit;;
val try_eq: signature -> context -> tERM -> tERM -> unit;;
val try_term: signature -> context -> tERM -> unit;;
val hOU: string list -> 
         (Term.signature * (int * int * int)) Link.linkedList -> signature;;
val intro_var:signature -> context -> string -> string -> tERM 
                -> tERM -> string -> unit;;
val apply_var:signature -> context -> string -> tERM -> tERM -> signature;;
val count_signature:signature -> (int*int*int);;
exception UnificationFailure;;
exception LimitExceeded;;
exception Solved;;

