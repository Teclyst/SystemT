Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import Definitions.Ident.
Require Import Definitions.Term.
Require Import Definitions.Type.
Require Import Definitions.Typing.
Require Import Definitions.Reduction.
Require Import Theorems.Reduction.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.
Open Scope system_t_type_scope.

Lemma normal_form_strongly_normalizing {e : termT} :
    normal_form e -> strongly_normalizing e.
Proof.
  intro Hnf.
  constructor.
  intros f Hred.
  destruct Hnf.
  exists f.
  assumption.
Qed.

Lemma strongly_normalizing_appT_inv_l {e f : termT} :
    strongly_normalizing (appT e f) ->
    strongly_normalizing e.
Proof.
  generalize (eq_refl (appT e f)).
  pattern (appT e f) at -1.
  generalize (appT e f) at -2.
  simpl.
  move=> g Heq Hsn.
  rewrite <- Heq in Hsn.
  move: Heq.
  move: e f.
  induction Hsn;
  move=> e f Heq.
  constructor.
  move=> h Hred.
  eapply (H0 (appT h f)).
  - rewrite Heq.
    unfold "1<-" in Hred.
    unfold "1<-".
    eauto using one_reduction.
  - reflexivity.
Qed.

Lemma strongly_normalizing_appT_inv_r {e f : termT} :
    strongly_normalizing (appT e f) ->
    strongly_normalizing f.
Proof.
  generalize (eq_refl (appT e f)).
  pattern (appT e f) at -1.
  generalize (appT e f) at -2.
  simpl.
  move=> g Heq Hsn.
  rewrite <- Heq in Hsn.
  move: Heq.
  move: e f.
  induction Hsn;
  move=> e f Heq.
  constructor.
  move=> h Hred.
  eapply (H0 (appT e h)).
  - rewrite Heq.
    unfold "1<-" in Hred.
    unfold "1<-".
    eauto using one_reduction.
  - reflexivity.
Qed.

Fixpoint reducibility_candidate (t : typeT) : termT -> Prop :=
  match t with
  | boolT =>
    fun e =>
      strongly_normalizing e /\ (exists b : bool, e ->* bool_as_boolT b)
  | natT =>
    fun e =>
      strongly_normalizing e /\ (exists n : nat, e ->* nat_as_natT n)
  | tvarT t =>
    strongly_normalizing
  | funT t u =>
    fun e =>
      forall f : termT,
      reducibility_candidate t f ->
      reducibility_candidate u (appT e f)
  end.

Lemma reducibility_candidate_sat1 {t :  typeT} {e f : termT} :
    reducibility_candidate t (e[O <- f]) ->
    strongly_normalizing f ->
    reducibility_candidate t (appT (absT e) f).
Proof.
  move: e f.
  induction t;
  simpl;
  move=> e f Hred Hsn.
Admitted.