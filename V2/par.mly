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
%token T_PYC T_DOT T_DOSP T_COMA T_TYPE T_TEST  T_KIND T_LET T_IN
%token T_BAS T_REL T_EQUAL T_FLECH T_WITH T_ASSIGN T_USING 
%token T_EOL
%token C_QUIT C_HELP C_CHECK C_VAR C_GOALS C_LEMMA C_METAVAR C_GO 
%token C_INTRO C_UNGOAL C_TRY C_APPLY C_SAVE C_SHOW C_COOK
%token C_UNIFY C_ETA C_BETA C_EVAL C_SIGMA C_RESOLVE C_LET
%token C_LIMIT C_VERBOSE C_LOAD C_RESETCTX C_SETCTX C_RESETSIG C_RESET
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
| C_SETCTX T_CORI rglSubs T_CORD {SetCtx($3)}
| C_VAR T_iden T_DOSP rglPreTerm      {Var($2,$4)}
| C_LET T_iden T_ASSIGN rglPreTerm    {Let($2,$4)}
| C_LEMMA  T_iden T_DOSP rglPreTerm   {MetaDecl(true,$2,$4)}
| C_METAVAR  T_iden T_DOSP rglPreTerm {MetaDecl(false,$2,$4)}
| C_UNGOAL {Ungoal}
| C_GOALS {Goals}
| C_RESOLVE using_ids {Resolve($2)}
| C_SAVE {Save("")}
| C_SAVE T_iden {Save($2)}
| C_GO T_IDEN {GoName($2)}
| C_GO T_INT {Go((-1)*$2)}
| C_GO {Go(0)}
| C_CHECK rglPreTerm {Check($2)}
| C_CHECK T_CORI rglSubs T_CORD {CheckS($3)}
| C_INTRO  {Intro("")}
| C_UNIFY rglPreTerm T_EQUAL rglPreTerm using_ids {Unify($5,$2,$4)}
| C_TRY   rglPreTerm T_EQUAL rglPreTerm {TryEq($2,$4)}
| C_TRY   rglPreTerm {Try($2)}
| C_APPLY rglPreTerm {Apply($2)}
| C_INTRO T_WITH T_iden {Intro($3)}
| C_BETA rglPreTerm{Eval(1,$2)}
| C_ETA  rglPreTerm {Eval(2,$2)}
| C_SIGMA rglPreTerm {Eval(3,$2)}
| C_EVAL rglPreTerm {Eval(0,$2)}
| C_LIMIT T_INT {Limit($2)}
| C_LOAD T_file {Load($2)}
| C_COOK T_INT {Cook($2)}
;

rglBound:
  T_iden T_DOSP rglTerm {str_ctx := $1::!str_ctx;
                         ($1,$3)}
| T_DOSP rglTerm {str_ctx := ""::!str_ctx;
                  ("",$2)} 
;

rglAnonymousBound:
  rglTerm T_FLECH {str_ctx := ""::!str_ctx;
                   $1}
;

list_anonymous:
  rglTerm {$1}
| rglAnonymousBound list_anonymous {str_ctx := tl !str_ctx; Pi("",$1,$2)}
;

rglPreTerm:
  T_COOKI rglTerm T_COOKD {cook 0 $2}
| T_COOKI T_INT T_DOSP rglTerm T_COOKD {cook $2 $4}
| rglTerm {$1}
;  

rglTerm:
  T_TYPE {Type}
| T_KIND {KIND}
| T_INT  {int2db $1 !str_ctx}
| T_iden {DB(name2db $1 !str_ctx)}
| T_IDEN {Metavar($1)}
| T_PARI rglTerm T_PARD {$2}
| T_PARI rglBound T_PARD rglTerm 
  {str_ctx := tl !str_ctx;
   match $2 with (a,b) -> Pi(a,b,$4)} 
| T_PARI list_anonymous T_PARD {$2}
| T_CUAI rglBound T_CUAD rglTerm 
  {str_ctx:= tl !str_ctx ;match $2 with (a,b) -> Lambda(a,b,$4)}
| T_PARI rglTerm list_terms T_PARD {unfoldl_app $2 $3}
| rglTerm T_CORI rglSubs T_CORD {Subs($1,$3)} 
| T_LET rglLet T_IN rglTerm 
  {str_ctx := tl !str_ctx; 
   match $2 with (nm,t,a) -> Subs($4,Cons(nm,t,a,Shift(0)))}
;

rglLet: 
  T_iden T_ASSIGN rglTerm T_DOSP rglTerm {str_ctx := $1::!str_ctx;($1,$3,$5)}
;

rglSubs:
  T_INT { if $1 < 0 then raise ConversionError else Shift($1) }
| T_iden T_ASSIGN rglTerm T_DOSP rglTerm T_DOT rglSubs {Cons($1,$3,$5,$7)}
|  rglTerm T_DOSP rglTerm T_DOT rglSubs {Cons("",$1,$3,$5)}
;

rglToEndOfLine:
    T_BAS T_EOL {()}
;
