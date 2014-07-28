type cTL_formula = Ff | Not of cTL_formula | And of cTL_formula * cTL_formula | AF of cTL_formula | EU of cTL_formula * cTL_formula | EX of cTL_formula |Atom of string;; 

type state = {name : string} ;;

type krypke_automaton = {k_initial: state list; k_q : state list; k_transition : (state * state) list; valuation : (state * (cTL_formula list)) list ;} ;;
(* Constructeurs logiques additionnels *)

let tt = Not Ff;;

let orr (f1,f2) =  Not (And (Not f1,Not f2));;

let implies (f1,f2) = or (Not f1) f2;;

let ax f1 = Not (EX (Not f1));;

let eg f1 = Not (AF (Not f1));;

let ef f1 = EU (tt,f1);;

let ag f1 = Not (ef (Not f1));;

let au (f1,f2) = Not (orr (  EU (Not f2, And (Not f1, Not f2)) , eg (Not f2)  ));;  

(* Opérations classiques sur les ensembles pris sous forme de listes *)

let without l1 l2 = List.filter (fun x -> not (List.mem x l2) ) l1;; (*  réalise lf1 privé de lf2 *)

let union l1 l2 = List.append l1 (List.filter (fun x -> not (List.mem x l1)) l2);;

let included l1 l2 = match without l1 l2 with (* est-ce que l1 inclut dans l2 *)
  |[] -> true
  |_ -> false;;

let inter l1 l2 = List.filter (fun x -> (List.mem x l2)) l1 ;;

 
(* Fonctions spécifiques à l'algorithme de model-checking en CTL*)

(* Pour un ensemble d'états S, pre_ex (S) renvoie l'ensemble des états q tels qu'il existe une transition de q à un état de S*)
let pre_ex state_set model = List.filter (fun x -> List.exists (fun y -> List.mem (x,y) model.k_transition ) state_set ) model.k_q;;

(* Pour un ensemble d'etat S, pre_fa (S) renvoie l'ensemble des états q tels que quelle que soit la transition de q vers q' existante, q' appartient à S *)
let pre_fa state_set model = without model.k_q (pre_ex (without model.k_q state_set) model);; (* on utilise le fait que pre_fa (S) est le complémentaire de pre_ex ( complémentaire de S) *)

let rec repeat prop app obj = if prop obj then obj else repeat prop app (app obj);; (* repeat répète l'opération 'app' sur 'obj' tant que 'prop obj' n'est pas vrai *)



(* ctl_sat model formula renvoie l'ensemble des états de 'model' marqués par la formule 'formula'. La fonction, récursive, suit l'algorithme classique de model-checking en CTL *)
let rec ctl_sat model formula =  match formula with
  |Ff -> [] (* Aucun état du modèle ne vérifie "false" *)
  |Not f -> without model.k_q (ctl_sat model f) (* Le complémentaire de l'ensemble d'états marqués par la formule 'f' *)
  |And (f1,f2) -> inter (ctl_sat model f1) (ctl_sat model f2) (* On ne veut que les états qui vérifient f1 et f2 d'où l'intersection *)
  |AF f ->
            let app y = {contents = union (y.contents) (pre_fa y.contents model)}
                     in
                        (repeat (fun y -> included (pre_fa y.contents model) (y.contents)) app (ref (ctl_sat model f)) ).contents
                
  |EU (f1,f2) ->

              let  app y = {contents = union (y.contents) (inter (ctl_sat model f1)  (pre_ex y.contents model))}
                 in
                       (repeat  (fun y -> (included (inter (ctl_sat model f1)  (pre_ex y.contents model))  (y.contents))    ) app (ref (ctl_sat model f2)) ).contents
                            
  |EX f ->  pre_ex (ctl_sat model f) model (* On va chercher les états q tels qu'il existe une transition de q à q' où q' est un état verifiant f i.e. marqué par f*)
  |Atom s -> List.filter (fun x -> List.mem (Atom s) (List.assoc x (model.valuation)) ) model.k_q (* cas trivial, on ne marque par 'Atom "p"' que les états dont 'Atom "p"' appartient à leur valuation *)

;;

(* Exemple *)
let model_test =
 { k_initial =[];
   k_q = [{name = "s0"};{name = "s1"};{name = "s2"};{name = "s3"};{name = "s4"};{name = "s5"};{name = "s6"};{name = "s7"};{name = "s9"}];

   k_transition = [({name = "s0"},{name = "s1"});({name = "s0"},{name = "s5"});({name = "s6"},{name = "s0"});({name = "s2"},{name = "s0"});({name = "s1"},{name = "s2"});
                   ({name = "s1"},{name = "s3"});({name = "s5"},{name = "s9"});({name = "s5"},{name = "s6"});({name = "s6"},{name = "s7"});({name = "s9"},{name = "s7"});
                   ({name = "s2"},{name = "s4"});({name = "s3"},{name = "s4"});({name = "s4"},{name = "s5"});({name = "s7"},{name = "s1"})];

   valuation = [({name = "s0"},[Atom "n1";Atom "n2"]);({name = "s1"},[Atom "t1";Atom "n2"]);({name = "s2"},[Atom "c1";Atom "n2"]);({name = "s3"},[Atom "t1";Atom "t2"]);({name = "s4"},[Atom "c1";Atom "t2"]);({name = "s5"},[Atom "n1";Atom "t2"]);({name = "s6"},[Atom "n1";Atom "c2"]);({name = "s7"},[Atom "t1";Atom "c2"]);
                   ({name = "s9"},[Atom "t1";Atom "t2"])]};;

(* Résultat connu: les états vérifiant EU (Not (Atom "c2"), Atom "c1") sont les états de "s0" à "s4" inclus *)

let model_check_ctl system formula = let set = (ctl_sat system formula) in included system.k_initial set;; (* Un automate de krypke 'system' verifie la propriété 'formula' si tous ses etats initiaux sont marqués par 'formula' après execution de 'ctl_sat system formula' *)
