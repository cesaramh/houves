(* pp.mli *)
open Term;;

val print_welcome: unit -> unit;;
val print_bye: unit -> unit;;
val print_prompt: signature -> unit;;
val print_help: unit -> unit;;
val comm_error: string -> int -> unit;;
val comm_mssg: int -> string -> unit;;
val print_term: string list -> tERM -> unit;;
val print_subs: string list -> sUBS -> unit;;
val print_sig: bool -> signature -> unit;;
val print_constr1: constraint0 -> bool -> unit;;
val print_constr2: constraint0 -> unit;;
val print_ctx2: context -> unit;;
val print_jud: contextName -> tERM -> tERM -> unit;;
val command_list: string list;;
exception ErrorMsg;;
