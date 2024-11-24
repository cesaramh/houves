(* Lexer *)
{ open Par;;
  exception Eof;;
  open String;;
  open Com;;
}

rule token = parse
       [' ' '\t'] {token lexbuf}         
     | ['\n']     {line := !line +1;
                   token lexbuf}
     | ['%'][^ '\n']* ['\n']    {line := !line+1;
                                 token lexbuf}
     | ['0'-'9']+ {T_INT(int_of_string(Lexing.lexeme lexbuf))}
     | ['-']['1'-'9']['0'-'9']* {T_INT(int_of_string(Lexing.lexeme lexbuf))}
     | "->"       {T_FLECH}
     | "with"     {T_WITH}
     | ":="       {T_ASSIG}
     | '='        {T_EQUAL}
     | '['        {T_CUAI}
     | ']'        {T_CUAD}
     | '('        {T_PARI}
     | ')'        {T_PARD}
     | '{'        {T_CORI}
     | '}'        {T_CORD}
     | "<<"       {T_COOKI}
     | ">>"       {T_COOKD}
     | ';'        {T_PYC}
     | '.'        {T_DOT}
     | ':'        {T_DOSP}
     | ','        {T_COMA}
     | '_'        {T_SUBG}
     | "|-"       {T_TEST}
     | "Type"     {T_TYPE}
     | "KIND"     {T_KIND}
     | "using"    {T_USING}
     | "Quit"     {C_QUIT}
     | "Help"     {C_HELP}
     | "Check"    {C_CHECK}
     | "Var"      {C_VAR}
     | "Show"     {C_SHOW}
     | "Lemma"    {C_LEMMA}
     | "Metavar"  {C_METAVAR}
     | "Goals"    {C_GOALS}
     | "Go"       {C_GO}
     | "Unvar"    {C_UNVAR}
     | "Ungoal"   {C_UNGOAL}
     | "Verbose"  {C_VERBOSE}
     | "Intro"    {C_INTRO}
     | "Limit"    {C_LIMIT}
     | "Load"     {C_LOAD}
     | "Try"      {C_TRY}
     | "Apply"    {C_APPLY}
     | "Save"     {C_SAVE}
     | "Define"   {C_DEFINE}
     | "Unify"    {C_UNIFY}
     | "Resolve"  {C_RESOLVE}
     | "Beta"     {C_BETA}
     | "Delta"    {C_DELTA}
     | "Eta"      {C_ETA}
     | "Eval"     {C_EVAL}
     | "Sigma"    {C_SIGMA}
     | "Section"  {C_SECTION}
     | "ResetCtx" {C_RESETCTX}
     | "ResetSig" {C_RESETSIG}
     | "Reset"    {C_RESET}
     | "End"      {C_END}
     | "Cook"     {C_COOK}
     | ['"']['a'-'z' 'A'-'Z' '_' ''' '-' '0'-'9' '/' '.']* ['"']
                  {let str = Lexing.lexeme lexbuf in
                     T_file(sub str 1 ((length str) - 2))}
     | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' ''' '0'-'9']* 
                  {T_iden(Lexing.lexeme lexbuf)}
     | ['#' 'a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_'  ''' '0'-'9']*['?' '!'] 
                  {T_IDEN(Lexing.lexeme lexbuf)}  
     | eof        {raise Eof} 

and  tokenToEndOfLine = parse
       [^ '\n']*  {T_BAS}
     | '\n'       {line := !line+1;T_EOL}



   
