
type lTL_formula = Atom of string | Not of lTL_formula | And of lTL_formula * lTL_formula | Or of lTL_formula * lTL_formula | U of lTL_formula * lTL_formula | X of lTL_formula |Tt|Ff  ;;

type node1 = {name_1 : string;};;

type buchi_automata = { q : node1 list; init : node1 list; transition : (node1 * node1) list; final : node1 list list; b_valuation : (node1 * lTL_formula list) list};;

type acc_mark = Acc of int;; (* Le type marque d'acceptation *)
 

(* Le type automate de Büchi généralisé à transitions marquées*)
type tgba = {q_set : node1 list; delta : (node1 * (acc_mark list) * node1) list; q_0 : node1; accepting_marks : acc_mark list};; (* Le type automate de Büchi généralisé à transitions marquées*)


let without l1 l2 = List.filter (fun x -> not (List.mem x l2) ) l1;; (*  réalise l1 privé de l2 *) 

let union l1 l2 = List.append l1 (List.filter (fun x -> not (List.mem x l1)) l2);; (* union de l1 et l2 *)

let included l1 l2 = match without l1 l2 with (* l1 inclut dans l2? *)
  |[] -> true
  |_ -> false;;

(* Transformation d'un automate de Büchi généralisé "classique" à un automate de Büchi généralisé à transitions marquées*)
(* 1ère étape: Faire en sorte qu'il n'y ait qu'un seul état initial -> on en crée un 'init' et on ajoute toutes les transitions de 'init' aux anciens états initiaux *) 


let adapt b_autom = 
 let init = {name_1 = "init_0"} 
                              in let i_transitions = List.map (fun x -> (init,x)) b_autom.init (* Liste des nouvelles transitions issues de'init'*)
                                       in
{q = init :: b_autom.q; (* ajout de 'init' à l'ensemble des états *)
 init = [init]; (* unique état initial *)
 transition = List.append i_transitions b_autom.transition; (* ajout des i_transitions *)
 final = b_autom.final;
 b_valuation = b_autom.b_valuation;};;





(* 2ème étape : Génération des marques d'acceptance que l'on affectera aux transitions *)

(* aux_mark sert de fonction auxiliaire à give_a_mark, qui prend en argument la liste des ensembles finaux d'acceptation d'un Büchi gén. et renvoie l'ensemble
 des couples (ensemble final d'acceptation, marque d'acceptation associée) *)
let rec aux_mark n accepting_set = match accepting_set with
  |[] -> []
  |h :: t -> (h,Acc n) :: (aux_mark (n-1) t);; 

let give_a_mark accepting_set = aux_mark (List.length accepting_set) accepting_set;;






(* Réalise le marquage des 'transitions' à partir d'un 'marked_final_sets' : liste des couples (ensemble final d'acceptation,marque d'acceptation associée) *)

(* La fonction est récursive en la variable 'marked_final_sets' car elle fonctionne comme suit:
   - on prend le premier ensemble d'acceptation.
   - on cherche toutes les transitions qui mènent à un état de cet ensemble.
   - on ajoute à ces transitions le marquage associé à l'ensemble d'acceptation.
   - on prend le second ensemble d'acceptation et on recommence.
   - Et ainsi de suite jusqu'à qu'on ait traité tous les ensembles finaux d'acceptation. *)
let rec marker marked_final_sets transitions = match marked_final_sets with
  |[] -> transitions (* il n'y a plus d'ens. final d'acceptation, on a fini le travail donc on renvoie les transitions*)
  |(set,mark) :: t -> let t1 = marker t transitions (* on suppose le marquage fait pour la queue de la liste des ensembles finaux d'acceptation, t1 est la liste des transitions résultantes *)
                  in
               List.map (fun (x,l,y) -> if List.mem y set then (x,mark::l,y) else (x,l,y) ) t1;; (* on traite ces transitions avec le "dernier" ensemble d'acceptation *)



(* Dernière étape: On peut maintenant construire la fonction qui renvoie l'automate sous sa forme adaptée à l'emptiness_check *)
let tgba_of_buchi b_autom =
                          let autom = adapt b_autom in (* autom est l'automate auquel on a imposé un unique état initial *)
                                     let marked_finals = (give_a_mark autom.final) in 
{q_set = autom.q ; 
 delta = marker marked_finals  (List.map (fun (x,y)-> (x,[],y)) autom.transition); (* marquage des transitions préparées à recevoir les marques d'acceptation *)
 q_0 = List.hd autom.init ; (* autom.init = [init] d'où la manoeuvre *)
 accepting_marks = List.map (fun (x,y) -> y) marked_finals ;};; (* on récupère les données de marked_finals qui nous intéressent *)


(* renvoie le numéro de visite du premier élément de la SCC *)
let top_n scc = let (n,a) = (Stack.pop scc) in Stack.push (n,a) scc; n  ;;

(* renvoie l'ensemble des états atteignables depuis un état q à partir des transitions delta *)
let reachable q delta = List.map (fun (x,l,y) -> y) (List.filter (fun (x,l,y) -> x = q)  delta);;

(* Met à jour la table de hashage en marquant comme mort (i.e numéro de visite = 0) les états renvoyés par reachable *)
let mark_reachable_states_as_dead (tgba,h_table) = List.iter (fun x -> Hashtbl.replace h_table tgba.q_0 0) (reachable tgba.q_0 tgba.delta);; 

(* Renvoie un automate identique au précédent à la différence près que l'état initial est s, cette fonction va permettre l'appel à la fonction emptiness_check dans le premier sous-cas de son algorithme *)
let tgba_from  tgba s = {q_set = tgba.q_set ; delta = tgba.delta; q_0 = s ; accepting_marks = tgba.accepting_marks ;};;

(* La fonction récursive qui reprend l'algorithme: elle répond à la question "Est qu'il n'existe aucune trace acceptante à partir de tgba.q_0?" *)
let rec emptiness_check (tgba, h_table, scc, acc) =

let current_state = tgba.q_0 (* l'état de départ *) and retour = ref false (* La référence qui contient la réponse à la question *) in
   
if not (Hashtbl.mem h_table current_state) (* Si l'état n'a pas encore été visité <=> pas encore recensé dans h_table *)
  then 
        let l0 = List.map (fun (x,l,y)-> (y,l)) (List.filter (fun (x,l,y)-> x = tgba.q_0) tgba.delta) (* liste des couples (état atteignable,marques d'acceptation de la transition associée)*) and h_q = (Hashtbl.length h_table) + 1 (* le numéro de visite que l'on va associer au nouvel état *) in
        begin
          Hashtbl.add h_table current_state (h_q); (* mise à jour de la h_table *)
          Stack.push (h_q,[]) scc; (* ajout de l'état dans la scc *)
        
           
          if aux_non_empty (tgba,h_table,scc,acc) l0 (* Cette fonction, récursive mutuellement avec emptiness_check, dont la définition est donnée plus bas, détermine s'il existe un état suivant à current_state tel que l'automate partant de cet état suivant soit non vide *)
              then 
            retour := false (* Si on a trouvé une trace acceptante alors on renverra false *)
          else (* Sinon, on a rien trouvé donc on renverra true*)
              begin
                if (top_n scc = h_q) (* Est-ce qu'après les tests effectués par aux_non_empty (qui ont agi d'une façon ou d'une autre sur la pile des SCC) on est exactement revenue au point de départ à savoir current_state? *)
                   then (* il faut éviter de reparcourir ces états "infructueux" en les marquant comme "morts" dans la h_table *)
                  begin
                  Stack.pop scc;
                  mark_reachable_states_as_dead (tgba,h_table)
                      end;
              retour:= true
              end;
         end


else (* Le current_state a déjà été visité *)
   let h_q =  Hashtbl.find h_table current_state (* le numéro de visite de current_state*) in
     if h_q = 0 (* Si l'état est mort *)
    then
       begin
       Stack.pop acc; (* On retire de acc les marques d'acceptation de la transition qui nous a menés à cet état mort *)
       retour := true; (* On est sur un état mort donc l'automate partant de cet état est vide *)
       end
    else (* l'état n'est pas mort -> on a bouclé *)
     begin  (* On rassemble dans la référence 'all' l'ensemble des marques d'acceptation de la boucle*)
     let elt  = ref (Stack.pop scc) in
     let all = ref (union (Stack.pop acc) (snd(!elt))) in
     while fst(!elt) > h_q do
     begin
     elt := Stack.pop scc;
     all := union (snd(!elt)) (union (Stack.pop acc) (!all))
     
     end
     done;

     begin
     Stack.push (fst(!elt),!all) scc; (* On ajoute à scc le noeud central de la boucle en question muni de 'all', si jamais une autre boucle est centrée sur ce même état alors on pourra ajouter ce 'all' à l'ensemble des marques d'acceptation de l'autre boucle et ainsi savoir si la combinaison de ces deux boucles est acceptante *)
     retour := not (included tgba.accepting_marks (!all)) (* Si la boucle est acceptante alors 'all' doit être égal à tgba.accepting_mark *)
     end;

       end
;
;
!retour

and  aux_non_empty (tgba,h_table,scc,acc) l = match l with (* Dans l'algorithme, l est la liste des (etat suivant, marques d'acceptation de la transition associée)  *)
  |[] -> false (* s'il n'y avait aucun état suivant alors l'automate était bien vide, donc non_empty - faux *)
  |(s,a) :: t ->  begin
                           Stack.push a acc; (* on ajoute à acc les marques d'acceptation de la transition menant à s*)
                           if emptiness_check (tgba_from tgba s, h_table, scc, acc) = false (* si l'automate à partir de s n'est pas vide *)
                           then true (* non_empty - true *)
                           else aux_non_empty (tgba,h_table,scc,acc) t (* sinon on regarde les autres états suivants *)
                  end

;;

(* fonction finale qui dit si un tgba est vide ou non *)
let is_empty tbga =  emptiness_check (tbga,Hashtbl.create 0,Stack.create (),Stack.create ());; 

    
let test_3 =
{q_set = [{name_1 = "1"};{name_1 = "2"};{name_1 = "3"};{name_1 = "4"};{name_1 = "5"};{name_1 = "6"};{name_1 = "7"};{name_1 = "8"};{name_1 = "9"};{name_1 = "10"};{name_1 = "11"};
{name_1 = "12"}];
 q_0 = {name_1 = "1"};
 delta = [({name_1 = "1"},[],{name_1 = "2"});({name_1 = "2"},[],{name_1 = "5"});({name_1 = "5"},[],{name_1 = "6"});({name_1 = "6"},[Acc 2],{name_1 = "11"});({name_1 = "11"},[],{name_1 = "12"});({name_1 = "12"},[],{name_1 = "5"});({name_1 = "6"},[],{name_1 = "10"});({name_1 = "10"},[],{name_1 = "9"});({name_1 = "9"},[],{name_1 = "6"});({name_1 = "6"},[Acc 2],{name_1 = "4"});({name_1 = "6"},[],{name_1 = "7"});({name_1 = "7"},[],{name_1 = "4"});({name_1 = "7"},[],{name_1 = "8"});({name_1 = "8"},[],{name_1 = "9"});({name_1 = "2"},[Acc 1;Acc 2],{name_1 = "3"});({name_1 = "3"},[Acc 1],{name_1 = "4"});({name_1 = "4"},[],{name_1 = "3"})] ;
 accepting_marks = [Acc 1;Acc 2];
};;

let test_4 =
{q_set = [{name_1 = "1"};{name_1 = "2"};{name_1 = "3"};{name_1 = "4"};{name_1 = "5"};{name_1 = "6"}];
 q_0 = {name_1 = "1"};
 delta = [({name_1 = "1"},[],{name_1 = "2"});({name_1 = "2"},[Acc 2],{name_1 = "3"});({name_1 = "3"},[],{name_1 = "5"});({name_1 = "5"},[Acc 3],{name_1 = "4"});({name_1 = "4"},[],{name_1 = "3"});({name_1 = "4"},[Acc 1],{name_1 = "2"});({name_1 = "2"},[Acc 1],{name_1 = "6"});({name_1 = "6"},[Acc 2],{name_1 = "6"})] ;
 accepting_marks = [Acc 1;Acc 2;Acc 3];
};;



#trace is_empty;;
is_empty test_3;;
is_empty test_4;;
