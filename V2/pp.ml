(* pp.ml *)
open Term;;
open Liblist;;
open Link;;
open List;;
open Com;;
open Version;;

exception ErrorMsg;;

let command_list = 
["\nCommands are:\n";
 "Quit, Help, Show, Goals, Verbose, Limit n, Load \"file\", Section sec, End sec\n\n";
 "Terms := Type | n | x | (x:A)M | (A->...->B) | [x:A]M | (M1 ... Mn) | (M){S} | let x:=M:A in N\n";
 "Subs := n | x:=M:A.S\n";
 "To precook M, use <<M>> or <<n:M>>\n\n";  
 "Tactics are: \n";
 "Var x:A\n"; 
 "Let x:=M\n";
 "Unvar\n";
 "Metavar X:A\n";
 "Lemma x:A\n";
 "Ungoal\n";
 "Check M, Check {S}\n";
 "Intro [with x]\n";
 "Apply M\n";
 "Save x\n";
 "Resolve [using sec1,...]\n";
 "Try M=N, Try M\n";
 "Unify M=N [using sec1,...]\n";
 "Eval M, Sigma M, Beta M\n";
 "Go x, Go n, Go\n";
 "Reset, ResetCtx, ResetSig, SetCtx S\n";
 "Cook n\n";
 ""];;

let print_welcome () =
    print_string "      +----------------------------------------------------+\n"; 
    print_string ("        Welcome to HOUVES "^version^"\n");
    print_string "        Higher-Order Unification via Explicit Substitutions\n";
    print_string "      +----------------------------------------------------+\n";
    print_string "\nTry with \"Help.\" for the list of valid commands.\n";
    flush stdout
;;

let print_bye () =
    print_string "Bye...\n\n";
    flush stdout
;;

let print_prompt sig0 =
    let prompt = 
      if is_empty_link sig0 then "> "
      else if sig0.pos = Nil then ">> " else
      (match(item_link 0 sig0) with
         Meta(_,_,nm,_) -> nm^"< "
       | Eq(_,_,_) -> "?==?< "
       | Assign(_,nm,_,_) -> nm^":=?< ")
    in
      print_string prompt;
      flush stdout
;;

let print_help () =
  let print_ehelp = function
    x -> print_string (x)
  in
  let print_list_help l = 
    print_list print_ehelp "" "" 
              "If \"Foo\" is a valid comand then type \"Foo.\"\n" 
              "" l in
  print_list_help command_list
;;

let mssg_error = function 
      1 -> "Syntax error"
    | 2 -> "Variable out of scope"
    | 3 -> "The section has been opened before"
    | 4 -> "Variable declarations are only valid in Types and Kinds"
    | 5 -> "Ill-typed term or substitution"
    | 6 -> "Lemma declarations are only valid in Types and Kinds"
    | 7 -> "The goal exists already"
    | 8 -> "The goal does not exist"
    | 9 -> "There is not a current goal"
    | 10 -> "The context is empty"
    | 11 -> ""
    | 12 -> ""
    | 13 -> ""
    | 14 -> "Tactic Intro does not apply"
    | 15 -> "Tactic Try does not apply"
    | 16 -> "Tactic Apply does not apply"
    | 17 -> "Tactic Save does not apply"
    | 18 -> "No goal to save"
    | 19 -> "The constant exists already"
    | 20 -> "Constant declarations are only valid in Objects and Types"
    | 21 -> "Tactic Unify does not apply"
    | 22 -> "Ill-type term"
    | 23 -> "The section has not been opened before"
    | 24 -> "The section has been closed before"
    | _ ->  "Unknown error"
;; 

let comm_error s code =
  let mssg = mssg_error code in
  print_string mssg;
  if s <> "" then (
    print_string ": \"";
    print_string s;
    print_string "\""
  );
  print_string " (line ";
  print_int !line;
  print_string ")";
  print_string ".\n";
  print_newline();
  raise ErrorMsg
;;

let comm_mssg code mss=
  (match code with
     1 -> print_string "Goal "
   | 2 -> print_string "Variable "  
   | _ -> print_string "Unknown message");
  print_string mss;
  (match code with
     1 -> print_string " has been proved."
   | 2 -> print_string " has been saved."  
   | _ -> print_string "");
  print_newline();
  flush stdout
;;

let rec app_names l = function
  Shift(n) -> cut_list n l 
| Cons(n,_,_,s)  -> n::app_names l s
| Comp(_,_) -> []
;; 

let rec print_term refer = function
  Type       -> print_string "Type"
| KIND       -> print_string "KIND"
| DB(n)      -> (try 
                   let s = (pos_list 1 n refer) in
                   if s="" then print_int n
                   else print_string s;
                 with _-> print_int n)
| Metavar(var) -> print_string var
| Pi("",a,k)  -> print_string "(";
                 print_term refer a;
                 print_string "->";
                 print_term (""::refer) k;
                 print_string ")"
| Pi(n,a,k)  -> print_string "(";
                print_string n;
                print_string ":"; 
                print_term refer a;
                print_string ")";
                print_term (n::refer) k
| Lambda(n,a,m) -> print_string "[";
                   print_string n;
                   print_string ":" ;
                   print_term refer a;
                   print_string "]";
                   print_term (n::refer) m
| App(m,n)      -> print_string "(";
                   print_term refer m;
                   print_string " "; 
                   print_term refer n;
                   print_string ")"
| Subs(m,s)     -> print_string "(";
                   print_term (app_names refer s) m;
                   print_string ")";
                   print_string "{";
                   print_subs refer s;
                   print_string "}"

and print_subs refer = function
  Shift(n) -> print_int n
| Cons(nm,m,a,s) -> 
                 if (nm <> "") then print_string (nm^":=");
                 print_term refer m; 
                 print_string ":";
                 print_term (app_names refer s) a; 
                 print_string ". ";
                 print_subs refer s
| Comp(s,t) -> print_subs refer s;
               print_string " o ";
               print_subs refer t
;;

let print_ctx c empty stri strl strr =
 (*  print_subs (get_var_names c) c *)
 print_subs [] c 
;;

(* if not full then print a simplified form of the constraint *)
let print_constr full empty str0 stri strl strr c b =
let print_c = function
  Meta(b,ctx,nm,a) -> if full then print_ctx ctx empty stri strl strr
                    else print_string "...";
                    print_string (
                    if full then "\n-------------\n" else " |- ");
                    print_string nm;
                    print_string ":";
                    print_term [] a
| Assign(ctx,nm,t,a) -> print_string "... |- ";
                        print_string nm;
                        print_string " := ";
                        print_term [] t;
                        print_string ":";
                        print_term [] a
| Eq(ctx,t1,t2)  -> print_string "... |- ";
                    print_term [] t1;
                    print_string "==";
                    print_term [] t2
in 
  if b then
    print_string str0;
  print_c c
;;

let print_constr1 = print_constr false "" "Actual goal is: " ", " "" "" 
;;

let print_constr2 c = 
  print_constr true "\n" "" "\n" "" "" c true;
  print_newline()
;;

let print_ctx2 ctx =
  print_ctx ctx  "No hypothesis.\n" "\n" "" "\n"
;;


(* if not full then print a simplified form of the signature *)
let print_sig full sig0 = print_link print_constr1  "No goals.\n" 
                          "\n" "" "\n" false sig0
;;

let print_jud refer t a =
  print_term refer t;
  print_string " : ";
  print_term refer a;
  print_newline()
;;

let print_jud_s refer s d =
  print_string "{";
  print_subs refer s;
  print_string "} : ";
  print_ctx2 d; 
  print_newline()
;;












