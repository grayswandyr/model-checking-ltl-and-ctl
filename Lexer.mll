{
type token =
  | ID of (string)
  | AND
  | OR
  | NOT
  | LPAREN
  | RPAREN
  | EOF
  | NEXT
  | UNTIL
  | ALWAYS
  | EVENTUALLY
  | IMPLIES
}

rule lex = parse
  | [' ' '\t']      { lex lexbuf }
  | "and"           { AND }
  | "or"            { OR }
  | "not"           { NOT }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "until"         { UNTIL }
  | "next"          { NEXT }
  | "eventually"    { EVENTUALLY } 
  | "always"        { ALWAYS }
  | "implies"       { IMPLIES }
  | ['A'-'Z' 'a'-'z' '_']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as s { ID (s) }
  | eof             { EOF }
