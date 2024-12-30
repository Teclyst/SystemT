Require Import types.
Require Import terms.
Require Import FSets.FMaps.
Require Import List.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

Module FMap := FIdent.Map.

Module FMapFacts := Coq.FSets.FMapFacts.WFacts FMap.

Module Context.

  Record t := {
    bmap : list typeT;
    fmap : FMap.t typeT
  }.

  Definition empty : t := {|
    bmap := List.nil;
    fmap := FMap.empty typeT
  |}.

  Definition map (f : typeT -> typeT) (G : t) := {|
    bmap := List.map f (bmap G);
    fmap := FMap.map f (fmap G)
  |}.

  Definition context_par_tsubst (s : TMap.t typeT) : t -> t :=
    map (typeT_par_tsubst s).

  Definition bpush (u : typeT) (G : t) := {|
    bmap := u :: (bmap G);
    fmap := fmap G
  |}.

  Definition Equal (G H : t) :=
    (bmap G) = (bmap H) /\ FMap.Equal (fmap G) (fmap H).
  
  #[export] Instance equivalence : Equivalence Equal.
  Proof.
    constructor; constructor; auto using FMapFacts.Equal_refl.
    - destruct H as [H _].
      rewrite H.
      reflexivity.
    - destruct H as [_ H].
      apply FMapFacts.Equal_sym.
      exact H.
    - destruct H as [H _].
      destruct H0 as [I _].
      rewrite H.
      rewrite I.
      reflexivity.
    - destruct H as [_ H].
      destruct H0 as [_ I].
      eapply FMapFacts.Equal_trans.
    --- exact H.
    --- exact I.
  Qed.

  Notation " x == y " := (Equal x y) (at level 70, no associativity).

  Notation " x =/= y " := (complement Equal x y) (at level 70, no associativity).

End Context.

Inductive derivation : Context.t -> termT -> typeT -> Prop :=
  | bvarT_ax :
    forall G : Context.t, forall n : nat, forall t : typeT,
    nth_error (Context.bmap G) n = Some t ->
    derivation G (bvarT n) t
  | fvarT_ax :
    forall G : Context.t, forall x : fident, forall t : typeT,
    FMap.MapsTo x t (Context.fmap G) ->
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

(** Given a type substitution and a typing derivation, applying
    that substitution to the context and all types appearing in the
    derivation yields a new derivation.
*)
Lemma derivation_par_tsubst
  {G : Context.t} {e : termT} {t : typeT}
  (s : TMap.t typeT) (D : derivation G e t) :
  derivation (Context.context_par_tsubst s G) e (typeT_par_tsubst s t).
Proof.
  induction D;
  eauto using derivation;
  simpl.
  - apply bvarT_ax.
    simpl.
    apply List.map_nth_error.
    exact H.
  - apply fvarT_ax.
    simpl.
    apply FMap.map_1.
    exact H.
Qed.

Lemma typing_id (t : typeT) :
    derivation Context.empty (absT (bvarT O)) (t ->T t).
Proof.
  eauto using derivation.
Qed.

Close Scope system_t_type_scope.
Close Scope system_t_term_scope.