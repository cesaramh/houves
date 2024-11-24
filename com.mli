(* com.mli *)
open Term;;

(* Machine command *)
type command = 
               Action of int (* >0=Error 0=Quit 1=Help 2=Verbose 3= Show *)
             | ParseError of string*int   (* token,line                  *)
             | Check  of tERM             (* Checking the type of a term *)
             | Cook of int                (* Reset cooking to n          *)
             | Var of string*tERM         (* Variable ident:type         *)
             | Goals                      (* Print goals                 *)
             | Unvar                      (* Undeclaration of variable   *)
             | Ungoal                     (* Undeclaration of goal       *)
             | Intro of string            (* Tactic Intro                *)
             | Intros of string           (* Tactics Intos               *)
             | MetaDecl of bool*string*tERM  (* MetaDecl (habitated?) 
                                                ident:type               *)
             | Load of string             (* Load file                   *)
             | GoName of string           (* Go ident?                   *)
             | Go of int                  (* Go n                        *)
             | Apply of tERM              (* Tactic Apply                *)
             | Save of string             (* Save proved goal            *)
             | Define of string*tERM      (* Define a constant           *)
             | Eval of int*tERM           (* Reduction of a term         *)
             | Unify of string list* tERM * tERM (* HOU                  *)
             | TryEq of tERM * tERM       (* Tactic Try                  *)
             | Try of tERM                (* Tactic Try                  *)
             | Resolve of string list     (* Resolve goals via HOU       *)
	     | Limit of int               (* Limit of HOU                *)
             | BeginSec of string         (* Begin Section               *)
             | EndSec of string           (* End Section                 *)
;;

val gOAL: signature;;
val cTX : context;;
val cOOK : int ref;;
val limit:int ref;;
val rULES : (tERM -> (bool*tERM)) list ref;;
val verbose:bool ref;;
val line: int ref;;
