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
Require Import Theorems.ChurchRosser.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.
Open Scope system_t_type_scope.

Lemma normal_form_reduction_star {e f : termT} :
    normal_form e -> (e ->* f) -> e = f.
Proof.
  intros Hnf Hred.
  destruct Hred as [n Hn].
  inversion Hn.
  - reflexivity.
  - destruct Hnf.
    exists f0.
    assumption.
Qed.

Lemma normal_form_equivalence {e f : termT} :
    normal_form e -> normal_form f ->
    e === f -> e = f.
Proof.
  intros Hnfe Hnff Hequiv.
  rewrite equivalence_reduction_star in Hequiv.
  destruct Hequiv as [g [Hredeg Hredfg]].
  apply (normal_form_reduction_star Hnfe) in Hredeg.
  apply (normal_form_reduction_star Hnff) in Hredfg.
  rewrite Hredeg.
  rewrite Hredfg.
  reflexivity.
Qed.

Lemma normal_form_fvarT {f : fident} :
    normal_form (fvarT f).
Proof.
  intro Hred.
  destruct Hred as [g Hred].
  inversion Hred.
Qed.

Lemma normal_form_bvarT {n : nat} :
    normal_form (bvarT n).
Proof.
  intro Hred.
  destruct Hred as [g Hred].
  inversion Hred.
Qed.

Lemma normal_form_absT {e : termT} :
    normal_form e ->
    normal_form (absT e).
Proof.
  intros Hnf Hred.
  destruct Hred as [g Hred].
  inversion Hred.
  apply Hnf.
  eexists.
  eauto.
Qed.

Lemma normal_form_trueT :
    normal_form trueT.
Proof.
  intro Hred.
  destruct Hred as [g Hred].
  inversion Hred.
Qed.

Lemma normal_form_falseT :
    normal_form falseT.
Proof.
  intro Hred.
  destruct Hred as [g Hred].
  inversion Hred.
Qed.

Lemma normal_form_oT :
    normal_form oT.
Proof.
  intro Hred.
  destruct Hred as [g Hred].
  inversion Hred.
Qed.

Lemma normal_form_sT {e : termT} :
    normal_form e ->
    normal_form (sT e).
Proof.
  intros Hnf Hred.
  destruct Hred as [g Hred].
  inversion Hred.
  apply Hnf.
  eexists.
  eauto.
Qed.

Lemma normal_form_bool_as_boolT {b : bool} :
    normal_form (bool_as_boolT b).
Proof.
  destruct b.
  - exact normal_form_trueT.
  - exact normal_form_falseT.
Qed.

Lemma normal_form_nat_as_natT {n : nat} :
    normal_form (nat_as_natT n).
Proof.
  induction n.
  - exact normal_form_oT.
  - eauto using normal_form_sT.
Qed.
