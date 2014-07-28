Du 30.06.14 au 01.08.14 j'ai effectué un stage d'un mois au département DTIM de l'ONERA.
J'ai étudié et implémenté en logique OCaml quelques algorithmes de model-checking pour les logiques temporelles LTL et CTL.

Comme il me restait un peu de temps, j'ai aussi implémenté un analyseur syntaxique reconnaissant les formules de type LTL. On peut très facilement adapter les codes associés (à savoir: Parser.mly, Lexer.mll, Main.ml et Formula.ml) pour faire un analyseur syntaxique pour CTL.

L'ouvrage de référence pour les algo est "Logic in Computer Science" de Michael Huth and Mark Ryan.

L'implémentation de l'algorithme de model checking pour CTL suit scrupuleusement l'ouvrage.

En ce qui concerne l'algorithme de model checking pour LTL, certaines pistes ont été développées:

  - La construction de l'automate reconnaissant la formule LTL se fait selon un processus dit "à la volée". Voir l'article 
"Simple On-The-Fly Automatic Verification of Linear Temporal Logic" de Gerth, Peled, Vardi and Wolper pour plus de détails. L'automate obtenu est un automate de Büchi généralisé (ensemble de sous-ensemble d'etats d'acceptation au lieu d'ensemble d'états d'acceptions). Il a donc fallu par la suite réflechir à comment faire la combinaison d'un automate de krypke (représentant le système dont on vérifie certaines propriétés) et d'un automate de Büchi généralisé.

  - J'ai été libre de choisir la méthode de vérification de la vacuité d'un automate de Büchi généralisé. J'ai adapté une méthode présentée par Alexandre Duret-Lutz dans l'article "Algorithmes pour la vérification de formules LTL
par l’approche automate".

Pour en revenir à l'analyse syntaxique, on compile le tout avec la commande:

ocamlbuild -use-menhir -menhir "menhir --external-tokens Lexer" Main.native

./Main.native démarre le parseur.
