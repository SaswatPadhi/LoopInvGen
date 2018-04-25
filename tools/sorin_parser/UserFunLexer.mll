(* File lexer.mll *)
{
	open UserFunParser
	exception Eof
}
rule token = parse
    [' ' '\t']  { token lexbuf }
  | ['\n' ]     { EOL }
  | ['0'-'9'] ['0'-'9']* as lxm { INT(lxm) }
  | ['A'-'Z' 'a'-'z']+ as lxm { VAR(lxm) }
  | '+'         { PLUS }
  | '-'			    { MINUS }
  | '*'         { TIMES }
  | '/'         { DIV }
  | '%'         { MOD }
  | '='         { EQ }
  | '>'         { GT }
  | '<'         { LT }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | "!="        { NEQ }
  | "<="        { LTEQ }
  | ">="        { GTEQ }
  | "||"        { OR }
  | "&&"        { AND }
  | eof         { raise Eof }