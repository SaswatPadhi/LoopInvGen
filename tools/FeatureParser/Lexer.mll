{
  open Parser

  exception Eof
}

rule token = parse
  | ['0'-'9']+ as lxm
    { INT(lxm) }
  | ['A'-'Z' 'a'-'z' '0' - '9' '.' '_' '!']+ as lxm
    { VAR(lxm) }

  | '('  { LPAREN }
  | ')'  { RPAREN }

  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { TIMES }
  | '/' { DIV }
  | '%' { MOD }

  | '='  { EQ }
  | '>'  { GT }
  | ">=" { GTEQ }
  | '<'  { LT }
  | "<=" { LTEQ }
  | "!=" { NEQ }

  | "&&" { AND }
  | "!"  { NOT }
  | "||" { OR }
  | "=>" { IMPLIES }

  | [' ' '\t'] { token lexbuf }
  | ['\n' ]    { EOL }
  | eof  { raise Eof }