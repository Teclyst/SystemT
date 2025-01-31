Require Import Definitions.Type.

Require Import List.
Require Import Morphisms.

Require Import ssreflect ssrfun ssrbool.

Lemma size_gt_O {t : typeT} : size t > O.
Proof.
  induction t;
  simpl;
  Lia.lia.
Qed.

#[export] Instance Equivalence_ext_equal : Equivalence ext_equal.
Proof.
  constructor.
  - move=> s t.
    reflexivity.
  - move=> r s Heq t.
    symmetry.
    auto.
  - move=> q r s Heq1 Heq2 t.
    transitivity (par_tsubst r t);
    auto.
Qed.

Lemma par_tsubst_empty {s : TMap.t typeT} {t : typeT} :
    TMap.Empty s -> t >> s = t.
Proof.
  move=> Hem.
  induction t;
  simpl;
  f_equal;
  auto.
  destruct (TMap.find s0 s) eqn:Heq;
  try reflexivity.
  destruct (Hem s0 t).
  apply TMap.find_2.
  assumption.
Qed.

Lemma par_tsubst_par_tsubst {s h : TMap.t typeT} {t : typeT} :
    (t >> s) >> h = t >> s >>> h.
Proof.
  induction t as [ | | k | t u | t u];
  simpl;
  f_equal;
  eauto.
  unfold tsubst_compose.
  rewrite TMapFacts.map2_1bis;
  destruct (TMap.find k s);
  simpl;
  destruct (TMap.find k h);
  reflexivity.
Qed.

Lemma tsubst_par_tsubst
  {s : TMap.t typeT} {x : TIdent.t} {t u : typeT} :
    tsubst x t (par_tsubst s u) =
    par_tsubst (tsubst_add_l x t s) u.
Proof.
  induction u  as [ | | k | u v | u v];
  simpl;
  f_equal;
  eauto.
  unfold tsubst_add_l.
  destruct (TMap.find x s) eqn:Heq1.
  - rewrite TMapFacts.map_o.
    destruct (TMap.find k s) eqn:Heq2.
  --- reflexivity.
  --- simpl.
      destruct TIdentFacts.eqb eqn:Heq3.
  ----- move/ TIdentFacts.eqb_spec in Heq3.
        rewrite Heq3 in Heq1.
        rewrite Heq2 in Heq1.
        discriminate Heq1.
  ----- reflexivity.
  - rewrite TMapFacts.add_o.
    rewrite TMapFacts.map_o.
    destruct (TMap.find k s) eqn:Heq2;
    destruct (TMapFacts.eq_dec x k) eqn:Heq3.
  --- rewrite e in Heq1.
      rewrite Heq1 in Heq2.
      discriminate Heq2.
  --- reflexivity.
  --- simpl.
      destruct (TIdentFacts.eqb x k) eqn:Heq4.
      reflexivity.
      move/ TIdentFacts.eqb_spec in Heq4.
      contradiction.
  --- simpl.
      destruct (TIdentFacts.eqb x k) eqn:Heq4.
      move/ TIdentFacts.eqb_spec in Heq4.
      contradiction.
      reflexivity.
Qed.

Lemma par_tsubst_size {x : TIdent.t} {s : TMap.t typeT} {t : typeT} :
    occurs x t = true ->
    size (tvarT x >> s) <= size (t >> s).
Proof.
  move=> Hocc.
  induction t;
  inversion Hocc.
  - move/ TIdentFacts.eqb_spec in H0.
    rewrite H0.
    reflexivity.
  - simpl (size (par_tsubst s (t1 ->T t2))).
    destruct (occurs x t1) eqn:Heq1.
  --- have Hle := IHt1 eq_refl.
      Lia.lia.
  --- simpl in H0.
      have Hle := IHt2 H0.
      Lia.lia.
  - simpl (size (par_tsubst s (t1 *T t2))).
    destruct (occurs x t1) eqn:Heq1.
  --- have Hle := IHt1 eq_refl.
      Lia.lia.
  --- simpl in H0.
      have Hle := IHt2 H0.
      Lia.lia.
Qed.

Lemma par_tsubst_tsubst
  {s : TMap.t typeT} {x : TIdent.t} {t u : typeT} :
    (u (|x |-> t|)) >> s = u >> (|x |-> t|) >>> s.
Proof.
  induction u  as [ | | k | u v | u v];
  simpl;
  f_equal;
  eauto.
  unfold tsubst_add_r.
  rewrite TMapFacts.add_o.
  destruct (TMapFacts.eq_dec x k) as [Heq1 | Heq1];
  destruct (TIdentFacts.eqb x k) eqn:Heq2;
  move/ TIdentFacts.eqb_spec in Heq2;
  unfold TMap.E.eq in Heq1;
  try contradiction;
  reflexivity.
Qed.

#[export] Instance Proper_tsubst_add_l :
    Morphisms.Proper
      (eq ==> eq ==> ext_equal ==> ext_equal)
      tsubst_add_l.
Proof.
  move=> x y Heq1 t u Heq2 r s Heq3 v.
  rewrite Heq1.
  rewrite Heq2.
  repeat rewrite <- tsubst_par_tsubst.
  f_equal.
  auto.
Qed.

#[export] Instance Proper_tsubst_add_r :
    Morphisms.Proper
      (eq ==> eq ==> ext_equal ==> ext_equal)
      tsubst_add_r.
Proof.
  move=> x y Heq1 t u Heq2 r s Heq3 v.
  rewrite Heq1.
  rewrite Heq2.
  repeat rewrite <- par_tsubst_tsubst.
  auto.
Qed.

#[export] Instance Proper_tsubst_compose :
    Morphisms.Proper
      (ext_equal ==> ext_equal ==> ext_equal)
      tsubst_compose.
Proof.
  move=> p q Heq1 r s Heq2 t.
  repeat rewrite <- par_tsubst_par_tsubst.
  rewrite Heq1.
  auto.
Qed.

Lemma tsubst_compose_assoc {q r s : TMap.t typeT} :
    q >>> r >>> s >>= q >>> (r >>> s).
Proof.
  move=> t.
  repeat rewrite <- par_tsubst_par_tsubst.
  reflexivity.
Qed.

#[export] Instance Preorder_tsubst_order :
    PreOrder tsubst_order.
Proof.
  constructor.
  - move=> s.
    exists (@TMap.empty _).
    unfold tsubst_order_with_tsubst.
    move=> t.
    rewrite <- par_tsubst_par_tsubst.
    symmetry.
    apply par_tsubst_empty.
    exact (@TMap.empty_1 _).
  - move=> q r s [p Hlep] [o Hleo].
    unfold tsubst_order_with_tsubst in Hlep, Hleo.
    exists (p >>> o).
    unfold tsubst_order_with_tsubst.
    rewrite <- tsubst_compose_assoc.
    rewrite <- Hlep.
    assumption.
Qed.

#[export] Instance Preorder_typeT_order :
    PreOrder typeT_order.
Proof.
  constructor.
  - move=> t.
    exists (@TMap.empty _).
    unfold typeT_order_with_tsubst.
    symmetry.
    apply par_tsubst_empty.
    exact (@TMap.empty_1 _).
  - move=> t u v [r Hler] [s Hles].
    unfold typeT_order_with_tsubst in Hler, Hles.
    exists (r >>> s).
    unfold typeT_order_with_tsubst.
    rewrite <- par_tsubst_par_tsubst.
    rewrite <- Hler.
    assumption.
Qed.

Lemma tsubst_nooccur
  {x: TIdent.t} {t u : typeT} :
    ~ TSet.In x (variable_set u) ->
    tsubst x t u = u.
Proof.
  induction u;
  simpl;
  auto;
  move=> Hnooccur.
  - destruct TIdentFacts.eqb eqn:Heq.
  --- move/TIdentFacts.eqb_spec in Heq.
      TSetFacts.fsetdec.
  --- reflexivity.
  - f_equal;
    try apply IHu1;
    try apply IHu2;
    TSetFacts.fsetdec.
  - f_equal;
    try apply IHu1;
    try apply IHu2;
    TSetFacts.fsetdec.
Qed.

Lemma tsubst_preserves_nooccur
  {x: TIdent.t} {t u : typeT} :
    ~ TSet.In x (variable_set t) ->
    ~ TSet.In x (variable_set (tsubst x t u)).
Proof.
  move=> Hnooccur.
  induction u;
  simpl;
  try destruct (TIdentFacts.eqb x s) eqn:Heq;
  simpl;
  try TSetFacts.fsetdec.
  move=> Hin.
  apply TSet.singleton_1 in Hin.
  move/ TIdentFacts.eqb_spec in Heq.
  unfold TSet.E.eq in Hin.
  apply Heq.
  symmetry.
  assumption.
Qed.

Lemma tsubst_subset {x : TIdent.t} {t u : typeT} :
    TSet.Subset
      (variable_set (tsubst x t u))
      (TSet.union
        (TSet.union (TSet.singleton x) (variable_set t))
        (variable_set u)).
Proof.
  induction u;
  simpl;
  try destruct (TIdentFacts.eqb x s) eqn:Heq;
  simpl;
  try TSetFacts.fsetdec.
Qed.

Lemma occurs_spec {x : TIdent.t} {t : typeT} :
    Bool.reflect (TSet.In x (variable_set t)) (occurs x t).
Proof.
  induction t;
  simpl;
  try right;
  try TSetFacts.fsetdec;
  try (
    destruct (occurs x t1);
    destruct (occurs x t2);
    inversion IHt1;
    inversion IHt2;
    try left;
    try right;
    TSetFacts.fsetdec
  ).
  destruct (TIdentFacts.eqb x s) eqn:Heq;
  try left;
  try right;
  move/ TIdentFacts.eqb_spec in Heq;
  TSetFacts.fsetdec.
Qed.

Lemma tsubst_compose_empty_r {s : TMap.t typeT} :
    s >>> (TMap.empty typeT) >>= s.
Proof.
  move=> t.
  rewrite <- par_tsubst_par_tsubst.
  rewrite par_tsubst_empty.
  - exact (TMap.empty_1 (elt := _)).
  - reflexivity.  
Qed.

Lemma tsubst_compose_empty_l {s : TMap.t typeT} :
    (TMap.empty typeT) >>> s >>= s.
Proof.
  move=> t.
  rewrite <- par_tsubst_par_tsubst.
  rewrite (par_tsubst_empty (s := (TMap.empty _))).
  - exact (TMap.empty_1 (elt := _)).
  - reflexivity.  
Qed.

Lemma tsubst_compose_tsubst_add_r {x : TIdent.t} {t: typeT}
  {r s : TMap.t typeT} :
    (|x |-> t|) >>> r >>> s >>= (|x |-> t|) >>> (r >>> s).
Proof.
  move=> u.
  rewrite <- par_tsubst_tsubst.
  repeat rewrite <- par_tsubst_par_tsubst.
  rewrite <- par_tsubst_tsubst.
  reflexivity.
Qed.

