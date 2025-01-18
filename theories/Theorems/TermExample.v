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
Require Import Theorems.NormalForm.
Require Import Theorems.StrongNormalization.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.
Open Scope system_t_type_scope.

Definition type_bool_as_boolT (b : bool) :
    |- bool_as_boolT b :T boolT :=
  match b with
  | true => trueT_ax Context.empty
  | _ => falseT_ax Context.empty
  end.

Fixpoint type_nat_as_natT (n : nat) :
    |- (nat_as_natT n) :T natT :=
  match n with
  | O => oT_ax Context.empty
  | S n =>
    sT_el Context.empty (nat_as_natT n) (type_nat_as_natT n)
  end.

Definition idT : termT := absT (bvarT O).

Definition notT : termT :=
  absT (iteT (bvarT O) falseT trueT).

Definition andT : termT :=
  absT (absT (iteT (bvarT O) (bvarT 1) falseT)).

Definition orT : termT :=
  absT (absT (iteT (bvarT O) trueT (bvarT 1))).

Definition addT : termT :=
  absT (absT
    (recT
      (bvarT O)
      (absT (absT (sT (bvarT (S O)))))
      (bvarT (S O)))).

Lemma type_idT {t : typeT} :
    |- idT :T t ->T t.
Proof.
  unfold idT.
  apply absT_in.
  unfold Context.bpush.
  simpl.
  apply bvarT_ax.
  unfold Context.bMapsTo.
  simpl.
  reflexivity.
Qed.

Lemma type_notT :
    |- notT :T boolT ->T boolT.
Proof.
  apply absT_in.
  unfold Context.bpush;
  unfold Context.empty;
  simpl.
  apply iteT_el;
  eauto using derivation.
  apply bvarT_ax.
  unfold Context.bMapsTo.
  simpl.
  reflexivity.
Qed.

Lemma type_andT :
    |- andT :T boolT ->T boolT ->T boolT.
Proof.
  apply absT_in.
  apply absT_in.
  unfold Context.empty;
  unfold Context.bpush;
  simpl.
  apply iteT_el;
  eauto using derivation;
  apply bvarT_ax;
  unfold Context.bMapsTo;
  simpl;
  reflexivity.
Qed.

Lemma type_orT :
    |- orT :T boolT ->T boolT ->T boolT.
Proof.
  apply absT_in.
  apply absT_in.
  unfold Context.empty;
  unfold Context.bpush;
  simpl.
  apply iteT_el;
  eauto using derivation;
  apply bvarT_ax;
  unfold Context.bMapsTo;
  simpl;
  reflexivity.
Qed.

Lemma type_addT :
    |- addT :T natT ->T natT ->T natT.
Proof.
  apply absT_in.
  apply absT_in.
  unfold Context.empty;
  unfold Context.bpush;
  simpl.
  apply recT_el; [ 
    |
    apply absT_in;
    apply absT_in;
    unfold Context.empty;
    unfold Context.bpush;
    simpl;
    apply sT_el |
  ];
  apply bvarT_ax;
  unfold Context.bMapsTo;
  simpl;
  reflexivity.
Qed.

Lemma idT_one_reduction {e : termT} : appT idT e ->1 e.
Proof.
  eauto using one_reduction.
Qed.

Lemma idT_spec {e : termT} : appT idT e ->* e.
Proof.
  exact (one_reduction_reduction_star idT_one_reduction).
Qed.

Lemma noT_spec {b : bool} :
    appT notT (bool_as_boolT b) ->* bool_as_boolT (~~ b).
Proof.
  exists 2.
  destruct b;
  eauto using one_reduction, reduction.
Qed.

Lemma andT_spec {b c : bool} :
    appT (appT andT (bool_as_boolT b)) (bool_as_boolT c) ->*
    bool_as_boolT (b && c).
Proof.
  exists 3.
  destruct b;
  destruct c;
  eauto using one_reduction, reduction.
Qed.

Lemma orT_spec {b c : bool} :
    appT (appT orT (bool_as_boolT b)) (bool_as_boolT c) ->*
    bool_as_boolT (b || c).
Proof.
  exists 3.
  destruct b;
  destruct c;
  eauto using one_reduction, reduction.
Qed.

Lemma bound_closed_nat_as_natT {n : nat} :
    bound_closed (nat_as_natT n).
Proof.
  induction n;
  unfold bound_closed;
  simpl;
  auto using bound_nclosed.
Qed.

Lemma bound_closed_bool_as_boolT {b : bool} :
    bound_closed (bool_as_boolT b).
Proof.
  destruct b;
  unfold bound_closed;
  simpl;
  auto using bound_nclosed.
Qed.

Lemma addT_spec {m n : nat} :
    appT (appT addT (nat_as_natT m)) (nat_as_natT n) ->*
    nat_as_natT (m + n).
Proof.
  induction m;
  simpl;
  unfold addT.
  - eapply red_star_next.
  --- apply redind_appT_l.
      apply redex_beta.
  --- simpl.
      eapply red_star_next.
  ----- apply redex_beta.
  ----- simpl.
        eapply red_star_next.
  ------- apply redex_recT_oT.
  ------- reflexivity.
  - eapply red_star_next.
  --- apply redind_appT_l.
      apply redex_beta.
  --- simpl.
      eapply red_star_next.
  ----- apply redex_beta.
  ----- simpl.
        eapply red_star_next.
  ------- apply redex_recT_sT.
  ------- simpl.
          rewrite Theorems.Substitution.bound_closed_bsubst;
          rewrite Theorems.Substitution.bound_closed_bshift;
          try (exact bound_closed_nat_as_natT).
          eapply red_star_next.
  --------- apply redind_appT_l.
            apply redex_beta.
  --------- simpl.
            eapply red_star_next.
  ----------- apply redex_beta.
  ----------- simpl.
              repeat rewrite Theorems.Substitution.bound_closed_bsubst;
              repeat rewrite Theorems.Substitution.bound_closed_bshift;
              try (exact bound_closed_nat_as_natT).
              apply reduction_star_sT.
              apply (normal_form_reduction_star_confluence
                (e := appT (appT addT (nat_as_natT m)) (nat_as_natT n))).
  ------------- exact normal_form_nat_as_natT.
  ------------- eapply red_star_next.
  --------------- apply redind_appT_l.
                  apply redex_beta.
  --------------- simpl.
                  eapply red_star_next.
  ----------------- apply redex_beta.
  ----------------- simpl.
                    rewrite Theorems.Substitution.bound_closed_bsubst;
                    rewrite Theorems.Substitution.bound_closed_bshift;
                    try (exact bound_closed_nat_as_natT).
                    reflexivity.
  ------------- assumption.
Qed.

Lemma bool_as_boolT_surj {e : termT} :
    |- e :T boolT -> exists b : bool, e ->* bool_as_boolT b.
Proof.
  move=> Hderiv.
  have Hredbool : reducibility_candidate boolT e.
  - apply reducibility_candidate_empty_derivation.
    assumption.
  - inversion Hredbool.
    assumption.
Qed.

Lemma nat_as_natT_surj {e : termT} :
    |- e :T natT -> exists n : nat, e ->* nat_as_natT n.
Proof.
  move=> Hderiv.
  have Hrednat : reducibility_candidate natT e.
  - apply reducibility_candidate_empty_derivation.
    assumption.
  - inversion Hrednat.
    assumption.
Qed.
