Require Import Definitions.Type.
Require Import Definitions.Term.
Require Import Definitions.Context.

Require Import FSets.FMaps.
Require Import List.

Lemma bMapsTo_fun {n : nat} {u v : typeT} {G : t} :
    bMapsTo n u G -> bMapsTo n v G -> u = v.
Proof.
  unfold bMapsTo.
  intros Hmapu Hmapv.
  rewrite Hmapu in Hmapv.
  inversion Hmapv.
  reflexivity.
Qed.

Lemma fMapsTo_fun {x : fident} {u v : typeT} {G : t} :
    fMapsTo x u G -> fMapsTo x v G -> u = v.
Proof.
  exact (@FMapFacts.MapsTo_fun _ _ _ _ _).
Qed.

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