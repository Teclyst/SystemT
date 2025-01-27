Require Import Definitions.Type.
Require Import Definitions.Term.
Require Import Definitions.Context.
Require Import Theorems.Type.

Require Import FSets.FMaps.
Require Import List.

Require Import ssreflect ssrfun ssrbool.

Lemma bMapsTo_fun {n : nat} {u v : typeT} {G : t} :
    bMapsTo n u G -> bMapsTo n v G -> u = v.
Proof.
  unfold bMapsTo.
  move=> Hmapu Hmapv.
  rewrite Hmapu in Hmapv.
  inversion Hmapv.
  reflexivity.
Qed.

Lemma fMapsTo_fun {x : FIdent.t} {u v : typeT} {G : t} :
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

#[export] Instance preorder : PreOrder context_tsubst_preorder.
Proof.
  constructor.
  - move=> G.
    exists (TMap.empty typeT).
    constructor.
  --- move=> n t Hmap.
      rewrite par_tsubst_empty.
  ----- exact (@TMap.empty_1 typeT).
  ----- assumption.
  --- move=> x t Hmap.
      rewrite par_tsubst_empty.
  ----- exact (@TMap.empty_1 typeT).
  ----- assumption.
  - move=> G H I [s [Hbmaps Hfmaps]] [h [Hbmaph Hfmaph]].
    exists (tsubst_compose s h).
    constructor.
  --- move=> n t HbmapG.
      rewrite <- par_tsubst_par_tsubst.
      exact (Hbmaph n (par_tsubst s t) (Hbmaps n t HbmapG)).
  --- move=> x t HbmapG.
      rewrite <- par_tsubst_par_tsubst.
      exact (Hfmaph x (par_tsubst s t) (Hfmaps x t HbmapG)).
Qed.

Lemma empty_context_tsubst_preorder_with_tsubst
  {s : TMap.t typeT} {G : t} :
    empty <|(s) G.
Proof.
  constructor.
  - move=> n t Hmap.
    unfold bMapsTo in Hmap. 
    destruct n;
    discriminate Hmap.
  - move=> x u Hmap.
    unfold fMapsTo in Hmap.
    destruct (FMap.empty_1 Hmap).
Qed.  

Lemma context_par_tsubst_context_tsubst_preorder_with_tsubst
  {s : TMap.t typeT} {G : t} {t : typeT} :
    G <|(s) context_par_tsubst s G.
Proof.
  destruct G.
  constructor.
  - move=> n u Hmap.
    unfold bMapsTo.
    simpl.
    unfold bMapsTo in Hmap.
    simpl in Hmap.
    rewrite List.nth_error_map.
    rewrite Hmap.
    reflexivity.
  - move=> x u Hmap.
    unfold fMapsTo.
    simpl.
    unfold fMapsTo in Hmap.
    simpl in Hmap.
    apply FMap.map_1.
    assumption.
Qed.

Lemma context_tsubst_preorder_with_tsubst_bpush
  {s : TMap.t typeT} {G H : t} {t : typeT} :
    G <|(s) H <-> bpush t G <|(s) bpush (par_tsubst s t) H.
Proof.
  constructor.
  - move=> [Hbmap Hfmap].
    constructor.
  --- move=> [ | n] u Hmap;
      unfold bMapsTo;
      simpl;
      unfold bMapsTo in Hmap;
      simpl in Hmap.
  ----- inversion Hmap.
        reflexivity.
  ----- fold (bMapsTo n u G) in Hmap. 
        fold (bMapsTo n (par_tsubst s u) H).
        auto.
  --- auto.
  - move=> [Hbmap Hfmap].
    constructor.
  --- move=> n u Hmap.
      exact (Hbmap (S n) u Hmap).
  --- auto.
Qed.
