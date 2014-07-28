(* Définition des types *)

type lTL_formula = Atom of string | Not of lTL_formula | And of lTL_formula * lTL_formula | Or of lTL_formula * lTL_formula | U of lTL_formula * lTL_formula | X of lTL_formula |Tt|Ff  ;;

type node  =  {name : string; mutable incoming : node list; neww : lTL_formula list; next : lTL_formula list; mutable old: lTL_formula list } ;;

(* Le noeud init *)

let init = {name = "init";incoming = []; neww = []; next = []; old = []};;

(* Fonctions prévues par l'algo on_the_fly *)


let new1 f = match f with
  |U (f1,f2) ->[f1]
  |Not (U (Not f1,Not f2))  -> [f2]
  |Or (f1,f2) -> [f1]
  |_ -> []
;;

let next1 f = match f with
|U (f1,f2)  -> [f]
|Not (U (Not f1,Not f2))  -> [f]
|_ -> []
;;

let new2 f = match f with
|U (f1,f2) -> [f2]
|Not U (Not f1,Not f2)  -> [f1;f2]
|Or (f1,f2) -> [f2]
|_ -> []
;;





(* Opérations classiques sur les ensembles pris sous forme de listes *)

let sup elt l = List.filter (fun x -> not (x = elt)) l;; (* suppression d'un élément *)

let without lf1 lf2 = List.filter (fun x -> not (List.mem x lf2) ) lf1;; (*  réalise lf1 privé de lf2 *)

let union l1 l2 = List.append l1 (List.filter (fun x -> not (List.mem x l1)) l2);;


(* Autres fonctions utiles à l'implémentation de l'algo on_the_fly *)

(* mise à jour de l'ensemble incoming de node1 avec la donnée de 'incoming'*)
let refreshed node1 incoming = {name = node1.name; incoming =  (union node1.incoming incoming); neww = node1.neww; next = node1.next; old = node1.old};;


(* Si les noeuds node1 et node2 ont les mêmes ensembles next et old alors on mets à jour l'ensemble incoming de node1 avec l'ensemble incoming de node2  *)
let maj node1 node2 = if (node1.next = node2.next) && (node1.old = node2.old) then refreshed node1 node2.incoming else node1;;


(* négation appliquée uniquement sur les litéraux, elle sert à détecter des inconsistances dans le dernier cas de filtrage de expand  *)
let neg f = match f with 
|Not Atom s -> Atom s
|Atom s -> Not (Atom s)
|f1 -> f1
;;


(* Fonction reconnaissant une certaine catégorie de formule, utilisée pour synthétiser le matching de expand *)
let cat f = match f with
|U (f1,f2) -> true
|Not U (Not f1,Not f2) -> true
|Or (f1,f2) -> true
|_ -> false;;



(* Implémentation de l'algo "On-the-fly" *)


let rec expand   (node , nodes_set) = match node.neww with

|[] -> 
   if List.exists (fun x -> (x.next = node.next) && (x.old = node.old)) nodes_set
        then 
               List.map (fun x -> maj x node ) nodes_set
        else 
               expand ( {name = node.name^".1"; incoming = [node]; neww = node.next ; next = []; old = []} , node :: nodes_set )


|And (f1,f2) :: l ->
   expand ( {name = node.name; incoming = node.incoming; neww =without (union node.neww (without [f1;f2] node.old)) [And (f1,f2)] ; next = node.next ; old = union node.neww [And (f1,f2)]} , nodes_set ) 

|f :: l when cat(f) ->
 
      let node1 = {name = node.name^".1" ; incoming = node.incoming ; neww =without (union node.neww (without (new1 f) node.old)) [f]; next = union node.next (next1 f); old = union node.old [f]}
      and node2 = {name = node.name^".2" ; incoming = node.incoming ; neww = without (union node.neww (without (new2 f) node.old)) [f]; next = node.next; old = union node.old [f]}
         
          in expand (node2, expand (node1, nodes_set))


|X f :: l ->
expand(   {name = node.name; incoming = node.incoming ; neww =without node.neww [X f]; next = union node.next [f]; old = union node.old [X f] }   ,nodes_set)
|p :: l -> if (p = Ff ||(List.mem (neg p) node.old))
              then nodes_set
           else 
              expand ({name = node.name; incoming = node.incoming ; neww =without node.neww [p]; next = node.next; old = union node.old [p] }, nodes_set)
;;


(* Création de l'automate: on applique l'expansion à partir du graphe initial suivant*)
let create_graph f =  expand ( {name = "1"; incoming = [init]; neww = [f]; next = []; old = []} , [] );;







(* Réécriture des noms des états *)

(* name_list renvoie la liste des noms des noeuds du graphe*)
let name_list nodes_set = List.map (fun x -> x.name) nodes_set;;

(* fonction auxiliaire réalisant le "nommage" à partir d'un entier fixé *)
let rec aux name_list n = match name_list with 
 |[] -> []
 |h :: t -> n :: aux t (n-1) ;;
(* intname name_list renvoie la liste des entiers qu'on associera aux différents noms: [n;n-1;n-2;...;1] où n est la taille de la liste de noms *)
let intname name_list = aux name_list (List.length name_list);;             

(* renvoie le nom entier associé à un nom de la ref_list . Par exemple new_name ["gerard";"michel";"elias"] "michel" =  "2", new_name ["gerard";"michel";"elias"] "gerard" = "3" *)
let new_name ref_list w =if w ="init" then "init" else  string_of_int (   List.assoc w (List.combine ref_list (intname ref_list)));;

(* Première fonction de renommage *)
let clear_autom nodes_set = 
 List.map (fun  node -> {name = new_name (name_list nodes_set) node.name; incoming = node.incoming; neww = node.neww; next = node.next; old = node.old}) nodes_set;;
(* On constate que le renommage n'est pas complet, en particulier ne sont concernés que les noms des noeuds du nodes_set*)



(* Automate un peu plus lisible, on renommera complètement l'automate de Büchi final à la fin *)
let create_graph_bis f = clear_autom (create_graph f) ;;






(* Ensembles d'états acceptants *)


(* Pour un U (f1,f2) identifié, renvoie l'ensemble d'états acceptants correspondant parmi les états dans nodes_set *)
let spot_set f1 f2 nodes_set = List.filter (fun x -> (not (List.mem (U (f1,f2)) x.old)) || (List.mem f2 x.old) ) nodes_set;;

(* Pour une formule 'formula' donnée, renvoie les ensembles d'états acceptants correspondant à chaque sous-formule de type U (f1,f2) *)
(* Parcourt la formule "en profondeur"*)
let rec final_state_sets formula nodes_set = match formula with
  |Atom s -> []
  |U (f1,f2) -> (spot_set f1 f2 nodes_set) :: (List.append (final_state_sets f1 nodes_set) (final_state_sets f2 nodes_set))
  |And (f1,f2) ->  List.append (final_state_sets f1 nodes_set) (final_state_sets f2 nodes_set)
  |Or (f1,f2) -> List.append (final_state_sets f1 nodes_set) (final_state_sets f2 nodes_set)
  |X f1 -> final_state_sets f1 nodes_set
  |Not f1 -> final_state_sets f1 nodes_set;;

(* Tests *)

let f =U (Atom "p",Atom "q");;
let autom = create_graph_bis f;; (* On prend create_graph_bis pour une meilleure lisibilité après exécution de la commande ci-dessous*)
let finaux = List.map (fun x-> List.map (fun y -> y.name) x) (final_state_sets f autom);; (* ensembles finaux d'acceptation de 'autom' *)







(* Réduction d'une formule LTL *)

(* Fonctions substituant les opérateurs additionnels F, G de LTL et l'implication en logique prépositionnelle *)

let eventually form = U (Tt,form);;

let always form = Not ( eventually (Not form));;

let implies f1 f2 = Or (Not f1, f2);;

(* Fonction de réduction LTL*)
(* Parcours en profondeur *)
let rec push_neg formula = match formula with
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
;;

(* Tests *)

let formula =Not( And (Not( U (Not (Not( Atom "p")),Atom "q")),U (Not (Not((Or( Atom "r", Not (Atom "t"))))),Not(Not( Atom "s")))) );;

push_neg formula;;






(* Etape finale: Renvoi de l'automate de Büchi *)

type node1 = {name_1 : string;};; 

type  buchi_automata = { q : node1 list; init : node1 list; transition : (node1 * node1) list; final : node1 list list; b_valuation : (node1 * lTL_formula list) list};;


(* Récupération des litéraux/négation de litéraux *)
let rec literal form_list = match form_list with
  |[] -> []
  |(Atom s) :: t -> (Atom s) :: (literal t)
  |(Not (Atom s) :: t) -> (Not (Atom s)) :: (literal t)
  |n :: t -> literal t;;  (* Récupération des litéraux/négation de litéraux *)

 (* Seuls les litéraux ou négation de litéraux de l'ensemble old nous intéressent pour la suite *)
let labelled node = literal node.old;; 

(* passage du format 'node' à 'node1' *)
let cleaned node = {name_1 = node.name;};;

(* ensemble des noeuds initiaux: noeuds tels que init est inclut dans leur incoming *)
let initial nodes_set =List.map (fun x -> cleaned x) ( List.filter (fun  x -> List.mem  init  (x.incoming)) nodes_set);;

let rec aux_t node  = List.map (fun x -> (x,node)) node.incoming;; (* L'ensemble des transitions que l'on peut déduire d'un noeud *) 

(* Calcul de l'ensemble des transitions à l'aide de nodes_set et de la fonction précédente*)
let rec transitions nodes_set = match nodes_set with
  |[]->[]
  |node::t -> List.append (aux_t node)  (transitions t);;

(* On exclut les transitions issues de 'init', ses suivants sont les vrais noeuds initiaux *)
let correct transitions = List.filter (fun (x,y) -> not (x.name_1 = "init") ) transitions;;




let on_the_fly formula = let nodes_set = create_graph formula (* on garde pour l'instant le nommage des noeuds en 1.1.2.1 etc...  *)
                             in
 { q = List.map (cleaned) nodes_set;
 init =  initial nodes_set;
 transition = correct ( List.map ( fun (x,y) -> (cleaned x,cleaned y)) (transitions nodes_set) );
 final = List.map (fun x -> List.map (cleaned) x) (final_state_sets formula nodes_set);
 b_valuation = List.map (fun x -> (cleaned x,labelled x)) nodes_set};;  

on_the_fly (U (Atom "p",Atom "q"));;

(* Renommage complet de l'automate *)


let name_list_2 q_set = List.map (fun x -> x.name_1) q_set;;

let rec aux name_list n = match name_list with
 |[] -> []
 |h :: t -> n :: aux t (n-1) ;;
let intname name_list = aux name_list (List.length name_list);;       (* On a repris certaines fonctions déjà définies avant *)      

let int_name_list name_list = List.map (fun x -> string_of_int x) name_list;;


let new_name_2 ref_list w =if w ="init" then "init" else List.assoc w (List.combine ref_list (int_name_list (intname (ref_list))));;

let rename_1 ref_list = (fun x -> {name_1 = new_name_2 ref_list x.name_1;});;
let rename_2 ref_list = (fun x -> List.map (rename_1 ref_list) x );;
let rename_3 ref_list = (fun (x,y) -> rename_1 ref_list x,rename_1 ref_list y);;

let clear_B_autom  autom =  let ref_list = name_list_2 autom.q in
 { q = List.map (rename_1 ref_list) autom.q;
 init =  List.map (rename_1 ref_list) autom.init;
 transition = List.map (rename_3 ref_list) autom.transition;
 final = List.map (rename_2 ref_list) autom.final ;
 b_valuation = List.map (fun (x,y) -> (rename_1 ref_list x,y) ) autom.b_valuation; } ;;

(* Résultat final *)

let on_the_fly_bis formula = clear_B_autom (on_the_fly formula);; (* Automate de Büchi bien plus facile à lire *)

(* Construction de l'automate produit *)

type state = {s_name : string} ;;

type krypke_automaton = {k_initial: state list;  k_q : state list; k_transition : (state * state) list; k_valuation : (state * (lTL_formula list)) list ;} ;;



(* Vérifie si les labels d'un 'state' de krypke et d'un 'node' de Büchi sont compatibles. on a besoin de leurs fonctions de valuation pour cela *)
let consistent k_model b_model state node = let lab_state =  (List.assoc state (k_model.k_valuation)) and lab_node =  (List.assoc node (b_model.b_valuation)) in
                                List.for_all (fun x -> not ((List.mem (neg (x)) lab_state))) lab_node;;

(* Réalise (('a * 'b) list -> ('c * 'd) list ---> ('a * 'c) * ('b * 'd) list) en vue de déterminer toutes les transitions potentielles de l'automate produit *)
let rec combine_1 l1 l2 = match l1 with
  |[] -> [] 
  |(a,b) :: t -> let l_temp =  (List.map (fun (x,y) -> (a,x),(b,y)  ) l2) in List.append l_temp (combine_1 t l2);;

(* Réalise la fusion d'un 'state' et d'un 'node', fonction qui va être très utilisée pour la réalisation de l'automate pduit *)
let fuse k_model b_model (a,b) =  let lab_a =  (List.assoc a (k_model.k_valuation)) and lab_b = (List.assoc b (b_model.b_valuation)) in
                           ({name_1 = a.s_name ^ "-" ^ b.name_1;}, union lab_a lab_b);;
  
(* Enlève les transitions générant des états incompatibles au niveau des labels *)
let clean_transitions k_model b_model transition_list = List.filter (fun ((a,b),(c,d)) ->  (consistent k_model b_model a b) && (consistent k_model b_model c d)) transition_list;;

(* A partir d'une liste de transitions renvoi la liste de tous les états concernés avec repetition possible de certains etats *)
let all_new_states transition_list = let (a,b) = List.split transition_list in List.append a b;;

(* Renvoie les transitions sous leur forme finale  *)
let set_transitions k_model b_model transition_list = List.map (fun ((w,x),(y,z)) -> (fst (fuse k_model b_model (w,x)), fst(fuse k_model b_model (y,z))) ) transition_list;;

(* Supprime toutes les multiples occurrences d'une liste *)
let rec sup_repetition l = match l with
  |[] -> []
  |a::t -> let l1 = sup_repetition t  in if List.mem a l1 then l1 else a::l1;;

(* Renvoie les états initiaux de l'automate produit, on regarde les couples dont au moins l'un des deux membres est un 'state'/'node' initial *)
let initials k_model b_model l = List.filter (fun (x,y) -> (List.mem x (k_model.k_initial) )&&(List.mem y b_model.init) ) l;;

(* Renvoie les ensembles d'états d'acceptation, i.e. les ensemble du type {  (a,b) tq b appartient à un ensemble d'acceptation F de *)
let final_sets b_model l = let b_final_sets = b_model.final in
              List.map (fun f_set ->  List.filter (fun (x,y) -> List.mem y f_set) l ) b_final_sets ;;

(* Fonction finale: renvoie l'automate produit de l'automate type krypke k_autom et de l'automate de büchi b_autom
                                    
 On procède comme suit:
- on combine les transitions des deux automates et on ne conserve que les transitions couplées "compatible" -> 'transition_1' dans le code
- on déduit de ces transitions couplées l'ensemble de tous les nouveaux noeuds (qui sont des couples de noeuds que l'on fusionnera avec 'fuse') de l'automate produit -> 'all_states' dans le code
- on renvoie le produit:
           ---> q = L'ensemble all_states auquel on a fait fusionner tous les couples de noeuds en un seul noeud de type node1
           ---> init = Initialement les couples (a,b) tels que a et b sont initiaux respectivement dans l'automate de krypke et celui de büchi généralisé
           ---> transition = Les transitions converties dans le bon format avec la fonction 'set_transitions'
           ---> final = on convertit au bon format le résultat de la fonction 'final_sets'
           ---> b_valuation = il suffit d'appliquer fuse à all_states.
                                                                                                      *)
let combined_automaton k_autom b_autom = 
                                          let transition_1 = clean_transitions k_autom b_autom ( combine_1 (k_autom.k_transition) (b_autom.transition) )
                                              in
                                           let  all_states = sup_repetition (all_new_states transition_1)
            in
 { q = List.map (fun x -> fst(fuse k_autom b_autom x)) all_states;
   init = List.map (fun x -> fst(fuse k_autom b_autom x)) (initials k_autom b_autom all_states);
   transition = set_transitions k_autom b_autom transition_1;
   final = List.map (fun x -> List.map (fun y -> fst(fuse k_autom b_autom y)) x ) (final_sets b_autom all_states);
   b_valuation = List.map (fuse k_autom b_autom) all_states;}

;;
                                                   
  
let model_test =
 { k_initial =[{s_name = "s0"}];
   k_q = [{s_name = "s0"};{s_name = "s1"};{s_name = "s2"};{s_name = "s3"};{s_name = "s4"};{s_name = "s5"};{s_name = "s6"};{s_name = "s7"};{s_name = "s9"}];

   k_transition = [({s_name = "s0"},{s_name = "s1"});({s_name = "s0"},{s_name = "s5"});({s_name = "s6"},{s_name = "s0"});({s_name = "s2"},{s_name = "s0"});({s_name = "s1"},{s_name = "s2"});
                   ({s_name = "s1"},{s_name = "s3"});({s_name = "s5"},{s_name = "s9"});({s_name = "s5"},{s_name = "s6"});({s_name = "s6"},{s_name = "s7"});({s_name = "s9"},{s_name = "s7"});
                   ({s_name = "s2"},{s_name = "s4"});({s_name = "s3"},{s_name = "s4"});({s_name = "s4"},{s_name = "s5"});({s_name = "s7"},{s_name = "s1"})];

   k_valuation = [({s_name = "s0"},[Atom "n1";Atom "n2"]);({s_name = "s1"},[Atom "t1";Atom "n2"]);({s_name = "s2"},[Atom "c1";Atom "n2"]);({s_name = "s3"},[Atom "t1";Atom "t2"]);({s_name = "s4"},[Atom "c1";Atom "t2"]);({s_name = "s5"},[Atom "n1";Atom "t2"]);({s_name = "s6"},[Atom "n1";Atom "c2"]);({s_name = "s7"},[Atom "t1";Atom "c2"]);
                   ({s_name = "s9"},[Atom "t1";Atom "t2"])]};;

let b_autom = on_the_fly_bis (U(Atom "p",Atom "q"));;

combined_automaton model_test b_autom;;
