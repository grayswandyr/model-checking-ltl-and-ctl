open Formula

let formula_of_string s = Parser.parse_formula Lexer.lex (Lexing.from_string s)

let _ = print_endline (string_of_formula (Formula.push_neg (formula_of_string (read_line ())))  )
