# Rapport de projet

## Historique approximatif du projet

- Premières définitions (termes, types, reductions, typage).
- Preuve de l'auto-réduction.
- Preuve de la confluence.
- Preuve de la normalisation forte.
- Rajout des types produits.
- Passage sous _dune_.
- Début du travail sur l'extraction de code et la partie _OCaml_ (l'interpréteur).
- Preuve de la correction et de la complétude de l'algorithme d'unification de Robinson.
- Preuve de la correction de l'algorithme de typage, et preuve partielle de sa complétude.

## Choix notables d'implémentation

### Variables libres et liées

J'ai dès le début fait le choix d'utiliser des indices de de Bruijn, et de distinguer deux types de variables (libres et liées). En effet, le fait d'utiliser des indices de de Bruijn implique qu'une variable liée fait toujours référence à un lambda plus haut (qu'il existe ou pas dans le terme), ce qui ne correspond pas vraiment à l'intuition qu'on aurait d'une variable libre. Ainsi, il y a une deuxième sorte de variables, indexées par des identifiants.

Plus tard dans le projet, le début du développement de l'interpréteur m'a conduit à changer la sémantique de ces variables libres, pour les interpréter plutôt comme des constantes déjà déclarées. En particulier, j'ai changé la manière dont les dérivations de typage sont définies pour que les types des variables liées soient polymorphiques (comme dans le système de typage de Hindley-Milner). L'intention étant qu'une suite de déclarations dans l'interpréteur comme la suivante soit acceptées:

```{bash}
let id x = x

let foo = id id
```

Dans l'état actuel des choses, essayer de rentrer ces déclarations dans le REPL donne bien la discussion suivante :

```{bash}
SystemT > let id x = x
val id : 'a -> 'a = fun x0 => x0 
SystemT > let foo = id id
val foo : 'a -> 'a = fun x0 => x0 
```

### Identifiants

Les identifiants pour les variables sont décrits par une signature de module. On demande un type ordonné muni d'une manière de créer des éléments frais (pour le typeur).

Pour les environnements et contextes de typage, j'ai choisi d'utiliser le module `FMap` de la librairie standard.

Par conséquent, l'implémentation des ensembles que j'utilise est `FSet` par cohérence, même si `MSet` est recommandé.

### Interpréteur

L'interpréteur peut recevoir deux types d'entrées :

- Terme à évaluer : entrée de la forme `e` où `e` est une expression. L'interpréteur essaie de la typer, et en cas de réussite la réduit, et affiche le type ainsi que la forme normale de `e`. Les variables libres présentent dans `e` sont toutes substituées par leur valeur dans l'environnement courant.
- Déclaration : entrée de la forme `let x = e` où `x` est un identifiant et `e` une expression. L'interpréteur essaie de la typer, et en cas de réussite la réduit, affiche son type et sa forme normale, et les rajoute dans l'environnement. Les variables libres présentent dans `e` sont toutes substituées par leur valeur dans l'environnement courant.

La terminaison de l'interpréteur est certifiable: en effet la correction des algorithmes est prouvée, ainsi que la normalisation forte pour le système T, et la compatibilité des substitutions parallèles de variables libres. En revanche, pour simplifier un peu le code, j'ai choisi d'écrire l'interpréteur en faisant appel à plusieurs sous-fonctions extraites de _Coq_, plutôt que d'écrire une seule fonction en _Coq_ représentant une étape d'exécution de l'interpréteur, et l'extraire.

Par ailleurs, l'interpréteur passe par un format intermédiaire (sans distinctions entre variables liées et libres, et sans indices de de Bruijn), qui est ensuite converti en le format extrait du code _Coq_. Cette conversion consiste essentiellement à repérer les variables liées et leur attribuer le bon indice. Aucune spécification n'est prouvée au sujet de cette étape.

Les types inférés sont aussi renommés (car le code _Coq_ produit beaucoup de noms de variables, qui fait que les indices augmentent très vite). Cette étape n'est pas non plus certifiée, car j'ai jugé que cela demanderait beaucoup d'effort pour pas grand chose ; cela dit, j'ai confiance en la correction du code.

L'interpréteur utilise le formatteur d'Ocaml, mais le pretty printer n'est pour l'instant pas très bien réglé.

### Stratégies utilisées pour les preuves

- Pour la confluence : réductions parallèles.
- Pour la normalisation forte : candidats de réductibilité de Girard.
- Pour le typeur : construction d'un problème d'unification "aussi général que possible" à partir d'un terme (dans le sens où les dérivations de typage de ce terme correspondent aux solutions du problème), puis résolution avec l'algorithme d'unification de Robinson.

## Difficultés rencontrées

### Substitutions

Une grande source de problèmes a été la gestion exacte des substitutions, qui demandent de faire attention à la gestion des indices. En particulier, la définition des substitutions parallèles de variables liées m'a pris du temps (bien qu'elle ne soit nécessaire que pour une petite partie de la preuve de normalisation forte).

### Normalisation forte

Sur la partie non-typage du projet, la propriété d'auto-réduction et la confluence ont été prouvées assez rapidement, mais la normalisation forte a pris beaucoup plus de temps, en plus ou moins trois étapes:

- D'abord, j'ai essayé d'adapter une preuve pour le lambda-calcul simplement typé utilisant des candidats de réductibilité vue dans le cours de lambda-calcul de Jean-Goubault Larrecq, mais avec la définition donnée dans celui de Thierry Joly (où par exemple $\mathrm R_{\mathrm{bool}}$ est défini comme l'ensemble des termes fortement normalisants pouvant être réduit vers `true` ou `false`). Cela a échoué car ces candidats de réductibilité ne vérifient pas les propriétés $(\mathrm{CR})$ de Girard. Mais je ne voulais pas abandonner cette définition, qui avait l'avantage de donner tout de suite qu'un terme de type `bool` (hors contexte) réduit vers `true` ou `false`, et de même qu'un terme de type `nat` réduit vers un entier (_i.e._ un terme de la forme ${\mathrm s}^n 0$).
- J'ai donc essayé de passer à la preuve de Thierry Joly, à base de lemmes de saturation. Mais malheureusement, la preuve était assez technique, et j'ai échoué à prouver le lemme de saturation pour $\mathrm{rec}$, car je n'ai pas réussi à trouver la bonne manière de faire marcher la récurrence sur l'accessibilité.
- Au final, je suis allé voir l'article original de Girard, et je me suis rendu compte qu'il était possible (et en fait assez simple) de montrer qu'un terme de type `bool` en forme normale est `true` ou `false`, et des résultats analogues pour les autres types. Une fois cette réserve levée, j'ai pu simplifier la définition des candidats de réductibilité pour qu'ils vérifient les propriétés $(\mathrm{CR})$ et faire marcher la preuve de Girard, et la preuve étant assez directe. La seule difficulté est venue encore une fois du cas $\mathrm{rec}$, où il a fallu faire une induction sur l'accessibilité pour un ordre produit lexicographique.

### Types dépendants

J'ai rencontré quelques problèmes lors de la définition de fonctions avec des types dépendants : principalement, comment faire un filtrage tout en récupérant une preuve d'égalité entre ce qui est filtré et le motif. Les recommandations trouvées sur _StackOverflow_, et le code obtenu en utilisant des tactiques, marchaient mal pour la suite car elles donnaient du code peu exploitables pour faire des preuves dessus : j'obtenais des erreurs de types dépendants quand j'essayais d'utiliser la tactique `destruct`. Ce genre de problèmes se sont surtout posés quand j'essayais de définir des fonctions par récursion sur l'accessibilité.

Au final, ma solution (un peu _ad hoc_) a été de m'inspirer du code dans [1] ; plus spécifiquement du fait de faire un filtrage sur `eq_dec`. Pour quelques types inductif, j'ai défini un wrapper qui construit à partir de preuves d'égalités avec un constructeur, pour pouvoir récupérer ces preuves dans le filtrage. Par exemple, pour `option` :

```{coq}
Inductive option_eq {A : Type} (opt : option A) :=
  | option_eq_Some : forall x : A, opt = Some x -> option_eq opt
  | option_eq_None : opt = None -> option_eq opt.
```

Filtrer sur `option_eq` permet d'obtenir une preuve d'égalité de `opt` à quelque chose, et donne du code sur lequel il est facile de raisonner.

### Typage

La certification de l'algorithme d'unification a eu lieu sans trop de problèmes ; en revanche, l'algorithme de construction de problème d'unification utilisé par le typeur a été beaucoup plus demandant (et d'ailleurs sa complétude n'est pas prouvée).

L'idée de l'algorithme n'est pas très dure a comprendre : parcourir le terme en créant à chaque niveau de nouvelles contraintes d'unification avec de nouvelles variables (une par niveau). La complétude vient alors essentiellement du fait qu'on utilise toujours des variables fraîches ; mais cela demande de bien contrôler les variables utilisées et est technique. La complétude consiste à montrer que le problème obtenu est "aussi général que possible", dans le sens où de toute dérivation de typage on peut obtenir une substitution qui satisfasse le problème ; une manière efficace de faire cela aurait été d'avoir une fonction de type (dépendant)

```{coq}
forall (G : Context.t) (t : typeT) (e : termT), G |- e :T t ->
TMap.t typeT
```

(Certains arguments auxiliaires sont omis de cette signature). Malheureusement, cela échoue car `G |- e :T t` est une proposition, qui ne peut donc pas être éliminée en une valeur d'un type. J'ai essayé de changer le type de `derivation` en `Context.t -> termT -> typeT -> Type`, mais cela a cassé d'autres choses dans le code.

Ainsi, je n'ai pas pu avoir une construction explicite de substitution ; à la place, j'ai dû me contenter de propositions existentielles directement dans l'énoncé de la preuve de complétude. Mais cela m'a forcé à donner un énoncé qui spécifie directement de nombreuses propriétés de contrôle sur les variables utilisées. Comme la preuve devenait trop compliquée par rapport au temps restant, j'ai fini par l'abandonner.

## Principales références utilisées

- [1] Xavier Leroy. _Well-founded recursion done right_.
- [2] Jean Goubault Larrecq. Cours de L3 de lambda-calcul à l'ENS Paris-Saclay.
- [3] Thierry Joly. Cours de théorie de la démonstration au LMFI.
- [4] Morten Heine B. Sørensen et Paweł Urzyczyn. _Lectures on the Curry-Howard isomorphism_.
- [5] Jean-Yves Girard, Paul Taylor et Yves Lafont. _Proofs and Types_.
- [6] Rodrigo Ribeiro et Carlos Camarão. _A Mechanized Textbook Proof of a Type Unification Algorithm_. Dans Márcio Cornélio et Bill Roscoe. _Formal Methods: Foundations and Applications_. (Ne contient pas directement de code _Coq_).