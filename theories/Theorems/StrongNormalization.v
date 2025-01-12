Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import Definitions.Ident.
Require Import Definitions.Term.
Require Import Definitions.Type.
Require Import Definitions.Typing.
Require Import Definitions.Reduction.
Require Import Theorems.Substitution.
Require Import Theorems.Reduction.
Require Import Theorems.NormalForm.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.
Open Scope system_t_type_scope.

(**
  We will later want to build elements of reducibility candidates.
  To avoid issues with bound variables gettting captured, we'll use
  one free variable instead.
   
  However, free variables idents are defined through an abstract
  signature to be generic, so we can't just find an example... or so
  it would seem. Indeed, we have the [Fident.new] function, which
  can be used over an empty [Fmap.t] to produce a default [fident].

  (For the current implementation for [nat] and [string], it would
  respectively be [1] and ["_"].)
*)
Definition default_fident := FIdent.new _ (FMap.empty unit).

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

Lemma strongly_normalizing_bsubst_inv {e f : termT} {n : nat} :
    strongly_normalizing (e[n <- f]) ->
    strongly_normalizing e.
Proof.
  generalize (eq_refl (e[n <- f])).
  pattern (e[n <- f]) at -1.
  generalize (e[n <- f]) at -2.
  simpl.
  move=> g Heq Hsn.
  rewrite <- Heq in Hsn.
  move: Heq.
  move: e f.
  induction Hsn;
  move=> e f Heq.
  constructor.
  move=> h Hred.
  eapply (H0 (h[n <- f])).
  - rewrite Heq.
    unfold "1<-" in Hred.
    unfold "1<-".
    eauto using one_reduction_bsubst_l.
  - reflexivity.
Qed.

Lemma strongly_normalizing_reduction_star {e f : termT} :
    (e ->* f) -> strongly_normalizing e ->
    strongly_normalizing f.
Proof.
  Admitted.

Lemma strongly_normalizing_redex_beta_inv {e f : termT} :
    strongly_normalizing (e[O <- f]) ->
    strongly_normalizing f ->
    strongly_normalizing (appT (absT e) f).
Proof.
  move=> Hsnsbst.
  have Hsne := strongly_normalizing_bsubst_inv Hsnsbst.
  move: Hsnsbst.
  move: f.
  induction Hsne as [e Hsne Hinde].
  move=> f Hsnsbst Hsnf.
  move: Hinde Hsne Hsnsbst.
  move: e.
  induction Hsnf as [f Hsnf Hindf].
  move=> e Hinde Hsne Hsnsbst. 
  constructor.
  move=> g Hred.
  inversion Hred; auto.
  - inversion H2.
    apply Hinde.
  --- unfold "1<-".
      assumption.
  --- eapply strongly_normalizing_reduction_star.
  ----- eapply reduction_star_bsubst_l.
        apply one_reduction_reduction_star.
        exact H4.
  ----- assumption.
  --- constructor.
      assumption.
  - apply Hindf.    
  --- unfold "1<-".
      assumption.
  --- assumption.
  --- exact Hsne.
  --- eapply strongly_normalizing_reduction_star.
  ----- eapply reduction_star_bsubst_r.
        apply one_reduction_reduction_star.
        exact H2.
  ----- assumption. 
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

Lemma reducibility_candidate_one_reduction {t : typeT} {e f : termT} :
    (e ->1 f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  move: e f.
  induction t; simpl; move=> e f Hred Hredue.
  - destruct Hredue as [Hsne [n Hredn]].
    constructor.
  --- apply Hsne.
      exact Hred.
  --- exists n.
      eapply normal_form_reduction_star_confluence.
  ----- exact normal_form_nat_as_natT.
  ----- apply one_reduction_reduction_star.
        exact Hred.
  ----- assumption.
  - destruct Hredue as [Hsne [b Hredb]].
    constructor.
  --- apply Hsne.
      exact Hred.
  --- exists b.
      eapply normal_form_reduction_star_confluence.
  ----- exact normal_form_bool_as_boolT.
  ----- apply one_reduction_reduction_star.
        exact Hred.
  ----- assumption.
  - apply Hredue.
    assumption.
  - move=> g Hredug.
    apply (IHt2 (appT e g));
    auto using one_reduction.
Qed.

Lemma reducibility_candidate_reduction {t : typeT} {e f : termT} {n : nat} :
    (e ->(n) f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  move=> Hred.
  induction Hred;
  eauto using reducibility_candidate_one_reduction.
Qed.

Lemma reducibility_candidate_reduction_star {t : typeT} {e f : termT} :
    (e ->* f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  intro Hred.
  destruct Hred.
  eauto using reducibility_candidate_reduction.
Qed.    

Fixpoint head_appT_list (e : termT) (l : list termT) : termT :=
  match l with
  | nil => e
  | cons f l => appT (head_appT_list e l) f
  end.

Lemma reducibility_candidate_sat_beta_aux {t :  typeT} {e f : termT} {l : list termT} :
    reducibility_candidate t (head_appT_list (e[O <- f]) l) ->
    strongly_normalizing f ->
    reducibility_candidate t (head_appT_list (appT (absT e) f) l).
Proof.
Admitted.

Lemma reducibility_candidate_sat_beta {t :  typeT} {e f : termT} :
    reducibility_candidate t (e[O <- f]) ->
    strongly_normalizing f ->
    reducibility_candidate t (appT (absT e) f).
Proof.
  exact (reducibility_candidate_sat_beta_aux (t := t) (e := e) (f := f) (l := nil)).
Qed.

Lemma reducibility_candidate_strongly_normalizing_aux {t : typeT} :
    (exists e : termT, reducibility_candidate t e /\ bound_closed e) /\
    (forall e : termT, reducibility_candidate t e -> strongly_normalizing e).
Proof.
  induction t;
    simpl.
  - constructor.
  --- exists (nat_as_natT O).
      (* With how things are defined, it is slighty easier to write
         [nat_as_natT O] instead of [oT]. *)
      constructor.
  ----- constructor.
  ------- apply normal_form_strongly_normalizing.
          exact normal_form_nat_as_natT.
  ------- exists O.
          reflexivity.
  ----- apply bound_closed_nat_as_natT.
  --- move=> e [Hsn _].
      assumption.
  - constructor.
  --- exists (bool_as_boolT false).
      constructor.
  ----- constructor.
  ------- apply normal_form_strongly_normalizing.
          exact normal_form_bool_as_boolT.
  ------- exists false.
          reflexivity.
  ----- apply bound_closed_bool_as_boolT. 
  --- move=> e [Hsn _].
      assumption.
  - constructor.
  --- exists (fvarT default_fident).
      constructor.
  ----- apply normal_form_strongly_normalizing.
        exact normal_form_fvarT.
  ----- unfold bound_closed.
        auto using bound_nclosed. 
  --- auto.
  - destruct IHt1 as [[e [Hredue Hbnde]] Hsne].
    destruct IHt2 as [[f [Hreduf Hbndf]] Hsnf].
    constructor.
  --- exists (absT f).
      constructor.
  ----- move=> g Hredug.
        apply reducibility_candidate_sat_beta.
  ------- rewrite (bound_closed_bsubst Hbndf).
          assumption.
  ------- auto.
  ----- unfold bound_closed.
        eauto using bound_nclosed, bound_closed_bound_nclosed.
  --- move=> g Hacc.
      eapply strongly_normalizing_appT_inv_l.
      apply Hsnf.
      apply Hacc.
      exact Hredue.
Qed.

Lemma reducibility_candidate_strongly_normalizing {t : typeT} {e : termT} :
    reducibility_candidate t e -> strongly_normalizing e.
Proof.
  move: e.
  exact reducibility_candidate_strongly_normalizing_aux.2.
Qed.
