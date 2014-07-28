%token <string> ID
%token AND NOT OR UNTIL NEXT ALWAYS EVENTUALLY IMPLIES
%token LPAREN RPAREN
%token EOF

%left OR AND
%nonassoc NOT

%{
  open Lexer
  open Formula
%}

%start parse_formula
%type <Formula.lTL_formula> parse_formula formula_expr

%%

%public formula_expr:
  | ID                                    { Atom ($1) }
  | NOT formula_expr                      { Not ($2) }
  | formula_expr AND formula_expr         { And ($1, $3) }
  | formula_expr OR formula_expr          { Or ($1,$3) }
  | formula_expr UNTIL formula_expr       { U ($1,$3) }
  | NEXT formula_expr                     { X ($2) }
  | LPAREN formula_expr RPAREN            { ($2) }
  | ALWAYS formula_expr                   { always ($2) }
  | formula_expr IMPLIES formula_expr     { implies ($1) ($3) }
  | EVENTUALLY formula_expr               { eventually ($2) }


parse_formula:
  | formula_expr EOF                      { $1 }
