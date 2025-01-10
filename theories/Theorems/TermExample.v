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
