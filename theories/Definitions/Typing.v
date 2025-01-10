Require Import Definitions.Type.
Require Import Definitions.Term.
Require Import Definitions.Context.
Require Import Theorems.Context.

Require Import FSets.FMaps.
Require Import List.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

Inductive derivation : Context.t -> termT -> typeT -> Prop :=
  | bvarT_ax :
    forall G : Context.t, forall n : nat, forall t : typeT,
    Context.bMapsTo n t G ->
    derivation G (bvarT n) t
  | fvarT_ax :
    forall G : Context.t, forall x : fident, forall t : typeT,
    Context.fMapsTo x t G ->
    derivation G (fvarT x) t
  | absT_in :
    forall G : Context.t, forall e : termT, forall t u : typeT,
    derivation (Context.bpush t G) e u ->
    derivation G (absT e) (t ->T u)
  | appT_el :
    forall G : Context.t, forall e f : termT, forall t u : typeT,
    derivation G e (t ->T u) ->
    derivation G f t ->
    derivation G (appT e f) u
  | trueT_ax :
    forall G : Context.t, derivation G trueT boolT
  | falseT_ax :
    forall G : Context.t, derivation G falseT boolT
  | iteT_el :
    forall G : Context.t, forall e f g : termT, forall t : typeT,
    derivation G e boolT ->
    derivation G f t ->
    derivation G g t ->
    derivation G (iteT e f g) t
  | oT_ax :
    forall G : Context.t, derivation G oT natT
  | sT_el :
    forall G : Context.t, forall e : termT,
    derivation G e natT ->
    derivation G (sT e) natT
  | recT_el :
    forall G : Context.t, forall e f g : termT, forall t : typeT,
    derivation G e t ->
    derivation G f (t ->T natT ->T t) ->
    derivation G g natT ->
    derivation G (recT e f g) t.

Notation "G |- e :T t" := (derivation G e t) (at level 90) : system_t_type_scope.
Notation "|- e :T t" := (derivation Context.empty e t) (at level 90) : system_t_type_scope.

Close Scope system_t_type_scope.
Close Scope system_t_term_scope.