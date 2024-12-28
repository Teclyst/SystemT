Require Import types.
Require Import terms.
Require Import FSets.FMaps.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

Module FMap := FMapPositive.PositiveMap.

Definition context := FMap.t typeT.

Print context.

(* Inductive typing_derivation : context -> termT -> typeT -> Type :=
  | var :
    forall G, forall n, forall t, G n = Some t ->
    TypingDerivation G (xT n) t
  | oTnatT :
    forall G, TypingDerivation G oT natT
  | sTnatT :
    forall G, forall e, TypingDerivation G e natT ->
    TypingDerivation G (sT e) natT. 
*)

Close Scope system_t_type_scope.
Close Scope system_t_term_scope.