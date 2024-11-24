%{
open List;;
open Term;;
open Com;;
open Liblist;;
%}

%token <int> T_INT
%token <string> T_IDEN
%token <string> T_iden
%token <string> T_file
%token T_CUAI T_CUAD T_PARI T_PARD T_CORI T_CORD T_COOKI T_COOKD T_SUBG
%token T_PYC T_DOT T_DOSP T_COMA T_TYPE T_TEST  T_KIND
%token T_BAS T_REL T_EQUAL T_FLECH T_WITH T_ASSIG T_USING 
%token T_EOL
%token C_QUIT C_HELP C_CHECK C_VAR C_GOALS C_LEMMA C_METAVAR C_GO 
%token C_UNVAR C_INTRO C_UNGOAL C_TRY C_APPLY C_SAVE C_SHOW C_COOK
%token C_DEFINE C_UNIFY C_ETA C_BETA C_DELTA C_EVAL C_SIGMA C_RESOLVE
%token C_LIMIT C_VERBOSE C_LOAD C_SECTION C_END C_RESETCTX C_RESETSIG C_RESET
%start main
%start rglToEndOfLine

%type <Com.command> main
%type <unit> rglToEndOfLine
%%
main:
  rglCommand T_DOT {$1}
;

list_idents:
  T_iden {[$1]}
| T_iden T_COMA list_idents {$1::$3}
;

list_terms:
  rglTerm {[$1]}
| rglTerm list_terms {$1::$2}  
;

using_ids:
  T_USING list_idents {$2}
| {[]}
;

rglCommand:
  C_QUIT {Action(0)}
| C_HELP {Action(1)}
| C_VERBOSE {Action(2)}
| C_SHOW  {Action(3)}
| C_RESETCTX {Action(4)}
| C_RESETSIG {Action(5)}
| C_RESET    {Action(6)}
| C_VAR  T_iden T_DOSP rglPreTerm      {Var($2,$4)}
| C_LEMMA  T_iden T_DOSP rglPreTerm    {MetaDecl(true,$2,$4)}
| C_METAVAR  T_iden T_DOSP rglPreTerm  {MetaDecl(false,$2,$4)}
| C_UNVAR {Unvar}
| C_UNGOAL {Ungoal}
| C_GOALS {Goals}
| C_RESOLVE using_ids {Resolve($2)}
| C_SAVE {Save("")}
| C_SAVE T_iden {Save($2)}
| C_GO T_IDEN {GoName($2)}
| C_GO T_INT {Go((-1)*$2)}
| C_GO {Go(0)}
| C_CHECK rglPreTerm {Check($2)}
| C_INTRO  {Intro("")}
| C_UNIFY rglPreTerm T_EQUAL rglPreTerm using_ids {Unify($5,$2,$4)}
| C_TRY   rglPreTerm T_EQUAL rglPreTerm {TryEq($2,$4)}
| C_TRY   rglPreTerm {Try($2)}
| C_APPLY rglPreTerm {Apply($2)}
| C_INTRO T_WITH T_iden {Intro($3)}
| C_DEFINE T_iden T_ASSIG rglPreTerm {Define($2,$4)}
| C_BETA rglPreTerm{Eval(1,$2)}
| C_DELTA rglPreTerm {Eval(2,$2)}
| C_ETA  rglPreTerm {Eval(3,$2)}
| C_SIGMA rglPreTerm {Eval(4,$2)}
| C_EVAL rglPreTerm {Eval(0,$2)}
| C_LIMIT T_INT {Limit($2)}
| C_LOAD T_file {Load($2)}
| C_SECTION T_iden {BeginSec($2)}
| C_END T_iden {EndSec($2)}
| C_COOK T_INT {Cook($2)}
;

rglBound:
  T_iden T_DOSP rglTerm {add_local_var $1 $3 cTX;
                         ($1,$3)}
| T_DOSP rglTerm {add_local_var "" $2 cTX;
                  ("",$2)} 
;

rglAnonymousBound:
  rglTerm T_FLECH {add_local_var "" $1 cTX;
                   $1}
;

list_anonymous:
  rglTerm {$1}
| rglAnonymousBound list_anonymous {un_var cTX; Pi("",$1,$2)}
;

rglPreTerm:
  T_COOKI rglTerm T_COOKD {cook 0 $2}
| T_COOKI T_INT T_DOSP rglTerm T_COOKD {cook $2 $4}
| rglTerm {$1}
;  

rglTerm:
  T_TYPE {Type}
| T_KIND {KIND}
| T_INT  {int2DB $1 cTX}
| T_iden {let pos = name2db $1 cTX in
          (match db2varType pos cTX with 
             TypeConst(_,t,_) -> Const(pos,Subs(t,Shift(pos)))
           | _ -> DB(pos))
         }
| T_IDEN {Metavar($1)}
| T_PARI rglBound T_PARD rglTerm 
  {un_var cTX;
   match $2 with (a,b) -> Pi(a,b,$4)} 
| T_PARI list_anonymous T_PARD {$2}
| T_CUAI rglBound T_CUAD rglTerm 
  {un_var cTX;match $2 with (a,b) -> Lambda(a,b,$4)}
| T_PARI rglTerm list_terms T_PARD {unfoldl_app $2 $3}
| T_PARI rglTerm T_PARD T_CORI rglSubs T_CORD {Subs($2,$5)}  
;

rglSubs:
  T_INT { if $1 < 0 then raise ConversionError else Shift($1) }
;

rglToEndOfLine:
    T_BAS T_EOL {()}
;
