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

Lemma normal_form_reduction_star_confluence {e f g : termT} :
    normal_form g -> (e ->* f) -> (e ->* g) -> (f ->* g).
Proof.
  intros Hnf Hredef Hredeg.
  destruct (confluence Hredef Hredeg) as [h [Hredfh Hredgh]].
  apply normal_form_reduction_star in Hredgh.
  - rewrite Hredgh.
    assumption.
  - assumption.  
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

Lemma normal_form_f_inv {r : termT -> termT} {e : termT} :
    (forall e f : termT, (e ->1 f) -> (r e ->1 r f)) -> 
    normal_form (r e) ->
    normal_form e.
Proof.
  intros Himpl Hnf Hred.
  destruct Hred as [g Hred].
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

Lemma normal_form_type {e : termT} {t : typeT} :
    normal_form e ->
    |- e :T t ->
      match t with 
        | boolT => exists b : bool, e = bool_as_boolT b
        | natT => exists n : nat, e = nat_as_natT n
        | t ->T u => exists f : termT, e = absT f
        | _ => True
      end.
Proof.
  move: t.
  induction e;
  move=> t Hnf Htype;
  inversion Htype.
  - destruct (FMap.empty_1 H1). 
  - destruct n;
    discriminate H1.
  - eauto.
  - destruct (IHe1 (t0 ->T t)).
  --- apply (normal_form_f_inv (r := fun e => appT e e2));
      eauto using one_reduction.
  --- assumption.
  --- rewrite H5 in Hnf.
      destruct Hnf.
      eexists.
      eauto using one_reduction.
  - exists true.
    auto.
  - exists false.
    auto.
  - destruct (IHe1 boolT).
  --- apply (normal_form_f_inv (r := fun e => iteT e e2 e3));
      eauto using one_reduction.
  --- assumption.
  --- rewrite H7 in Hnf.
      destruct Hnf.
      destruct x;
      eexists;
      eauto using one_reduction.
  - exists O.
    auto.
  - destruct (IHe natT).
  --- apply (normal_form_f_inv (r := sT));
      eauto using one_reduction.
  --- assumption.
  --- exists (S x).
      rewrite H3.
      reflexivity.
  - destruct (IHe3 natT).
  --- apply (normal_form_f_inv (r := recT e1 e2));
      eauto using one_reduction.
  --- assumption.
  --- rewrite H7 in Hnf.
      destruct Hnf.
      destruct x;
      eexists;
      eauto using one_reduction.
Qed.
