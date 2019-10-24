%token DIV MOD MINUS PLUS TIMES
%token EQ GT GTEQ LT LTEQ NEQ
%token AND IMPLIES NOT OR
%token LPAREN RPAREN
%token EOL

%token <string> INT
%token <string> VAR

%left AND IMPLIES OR            /* lowest precedence  */
%left NOT
%left NEQ EQ LTEQ GTEQ LT GT    /* m1 precedence      */
%left PLUS MINUS                /* m2 precedence      */
%left TIMES DIV MOD             /* highest precedence */

%start main

%type <string> main

%%

main:
  expr EOL               { $1 }
;

expr:
  | INT                  { $1 }
  | VAR                  { $1 }
  | LPAREN expr RPAREN   { $2 }

  | MINUS expr           { "(- 0 " ^ $2 ^ ")" }

  | expr DIV expr        { "(div " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr MINUS expr      { "(- " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr MOD expr        { "(mod " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr PLUS expr       { "(+ " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr TIMES expr      { "(* " ^ $1 ^ " " ^ $3 ^ ")" }

  | expr EQ expr         { "(= " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr GT expr         { "(> " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr GTEQ expr       { "(>= " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr LT expr         { "(< " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr LTEQ expr       { "(<= " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr NEQ expr        { "(not (= " ^ $1 ^ " " ^ $3 ^ "))" }

  | NOT expr             { "(not " ^ $2 ^ ")" }
  | expr AND expr        { "(and " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr IMPLIES expr    { "(=> " ^ $1 ^ " " ^ $3 ^ ")" }
  | expr OR expr         { "(or " ^ $1 ^ " " ^ $3 ^ ")" }
;