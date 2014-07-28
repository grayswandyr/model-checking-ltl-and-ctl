type lTL_formula =
| Atom of string
| Not of lTL_formula 
| And of lTL_formula * lTL_formula 
| Or of lTL_formula * lTL_formula 
| U of lTL_formula * lTL_formula 
| X of lTL_formula 
|Tt
|Ff 

let eventually form = U (Tt,form) 

let always form = Not ( eventually (Not form))

let implies f1 f2 = Or (Not f1, f2)

let rec string_of_formula f = match f with
|Atom s -> s
|Not p -> "Not ( " ^ (string_of_formula p) ^ " )"
|And (u,v) -> " ( " ^ (string_of_formula u) ^ " And " ^ (string_of_formula v) ^ " )"
|Or (u,v) -> " ( " ^ (string_of_formula u) ^ " Or " ^ (string_of_formula v) ^ " )"
|U (u,v) -> " ( " ^ (string_of_formula u) ^ " Until " ^ (string_of_formula v) ^ " )"
|X p -> " Next ( " ^ (string_of_formula p) ^ " )"
|Tt -> " True "
|Ff -> " False " 
    
let rec push_neg formula = match formula with (* Reduction d'une formule LTL *)
  |Not (Not f1) -> push_neg f1 (* on simplifie les doubles négations*)
  |Not (And (f1,f2)) -> Or (push_neg (Not f1), push_neg (Not f2)) (* Lois de De Morgan *)
  |Not (Or (f1,f2)) -> And (push_neg (Not f1), push_neg (Not f2)) (* Lois de De Morgan *)
  |Not (X f1) -> X (push_neg (Not f1))
  |Not (U (f1,f2)) -> Not (U (push_neg f1,push_neg f2)) (* On conserve les "Not U ( , )" *)
  |And (f1,f2) -> And (push_neg f1, push_neg f2)
  |Or (f1,f2) ->  Or (push_neg f1, push_neg f2)
  |X f1 ->  X (push_neg f1)
  |U (f1,f2) ->  U (push_neg f1, push_neg f2)
  |Not (Tt) -> Ff (* Cas trivial mais important *)
  |Not (Ff) -> Tt (* Cas trivial mais important *)
  |_ -> formula
