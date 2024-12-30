Require Import types.
Require Import terms.
Require Import FSets.FMaps.
Require Import List.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

Module FMap := FIdent.Map.

Record context := {
  bmap : list typeT;
  fmap : FMap.t typeT
}.

Definition bpush (t : typeT) (G : context) := {|
  bmap := t :: (bmap G);
  fmap := fmap G
|}.

Inductive typing_derivation : context -> termT -> typeT -> Type :=
  | bvarT_ax :
    forall G : context, forall n : nat, forall t : typeT,
    nth_error (bmap G) n = Some t ->
    typing_derivation G (bvarT n) t
  | fvarT_ax :
    forall G : context, forall x : fident, forall t : typeT,
    FMap.MapsTo x t (fmap G) ->
    typing_derivation G (fvarT x) t
  | absT_in :
    forall G : context, forall e : termT, forall t u : typeT,
    typing_derivation (bpush t G) e u ->
    typing_derivation G (absT e) (t ->T u)
  | appT_el :
    forall G : context, forall e f : termT, forall t u : typeT,
    typing_derivation G e (t ->T u) ->
    typing_derivation G f t ->
    typing_derivation G (appT e f) u
  | trueT_ax :
    forall G : context, typing_derivation G trueT boolT
  | falseT_ax :
    forall G : context, typing_derivation G falseT boolT
  | iteT_el :
    forall G : context, forall e f g : termT, forall t : typeT,
    typing_derivation G e boolT ->
    typing_derivation G f t ->
    typing_derivation G g t ->
    typing_derivation G (iteT e f g) t
  | oT_ax :
    forall G : context, typing_derivation G oT natT
  | sT_el :
    forall G : context, forall e : termT, typing_derivation G e natT ->
    typing_derivation G (sT e) natT
  | recT_el :
    forall G : context, forall e f g : termT, forall t : typeT,
    typing_derivation G e t ->
    typing_derivation G f (t ->T natT ->T t) ->
    typing_derivation G g natT ->
    typing_derivation G (recT e f g) t.

Close Scope system_t_type_scope.
Close Scope system_t_term_scope.