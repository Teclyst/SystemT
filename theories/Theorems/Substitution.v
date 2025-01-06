Require Import Definitions.Term.
Require Import Lia.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.

Lemma bshift_bshift {e : termT} {m n : nat} :
    m <= n -> bshift m (bshift n e) = bshift (S n) (bshift m e).
Proof.
  move: m n.
  induction e;
  move=> m' n' H4;
  eauto;
  simpl.
  - destruct (PeanoNat.Nat.leb n' n) eqn:H1;
    destruct (PeanoNat.Nat.leb m' n) eqn:H2;
    move/ PeanoNat.Nat.leb_spec0 in H1;
    move/ PeanoNat.Nat.leb_spec0 in H2;
    try lia;
    simpl.
  --- rewrite Compare_dec.leb_correct.
      lia.
      rewrite Compare_dec.leb_correct.
      auto.
      reflexivity.
  --- rewrite Compare_dec.leb_correct.
      auto.
      rewrite Compare_dec.leb_correct_conv.
      lia.
      reflexivity.
  --- rewrite Compare_dec.leb_correct_conv.
      lia.
      destruct n.
  ----- reflexivity.
  ----- rewrite Compare_dec.leb_correct_conv.
        lia.
        reflexivity.
  - rewrite IHe.
    lia.
    reflexivity.
  - rewrite (IHe1 _ _ H4).
    rewrite (IHe2 _ _ H4).
    reflexivity.
  - rewrite (IHe1 _ _ H4).
    rewrite (IHe2 _ _ H4).
    rewrite (IHe3 _ _ H4).
    reflexivity.
  - rewrite (IHe _ _ H4).
    reflexivity.
  - rewrite (IHe1 _ _ H4).
    rewrite (IHe2 _ _ H4).
    rewrite (IHe3 _ _ H4).
    reflexivity.
Qed.

Lemma bshift_bsubst_eq {e f : termT} {n : nat} :
    (bshift n e) [n <- f] = e.
Proof.
  move: f n.
  induction e;
  move=> g m;
  eauto;
  simpl;
  try (f_equal;
    auto).
  destruct (PeanoNat.Nat.leb m n) eqn:H1;
  move/ PeanoNat.Nat.leb_spec0 in H1;
  simpl.
  - destruct (PeanoNat.Nat.compare m (S n)) eqn:H2.
  --- rewrite PeanoNat.Nat.compare_eq_iff in H2.
        lia.
  --- rewrite PeanoNat.Nat.compare_lt_iff in H2.
        reflexivity.
  --- try rewrite PeanoNat.Nat.compare_gt_iff in H2.
        lia.
  - destruct (PeanoNat.Nat.compare m n) eqn:H2.
  --- rewrite PeanoNat.Nat.compare_eq_iff in H2.
        lia.
  --- rewrite PeanoNat.Nat.compare_lt_iff in H2.
        lia.
  --- try rewrite PeanoNat.Nat.compare_gt_iff in H2.
        reflexivity.
Qed.

Lemma bshift_bsubst {e f : termT} {m n : nat} :
    m <= n -> bshift n (e[m <- f]) = (bshift (S n) e)[m <- bshift n f].
Proof.
  move: f m n.
  induction e;
  move=> f' m' n' H4;
  eauto.
  - simpl;
    destruct (PeanoNat.Nat.compare m' n') eqn:H1;
    destruct (PeanoNat.Nat.compare m' n) eqn:H2;
    destruct (PeanoNat.Nat.compare n n') eqn:H3;
    try rewrite PeanoNat.Nat.compare_eq_iff in H1;
    try rewrite PeanoNat.Nat.compare_eq_iff in H2;
    try rewrite PeanoNat.Nat.compare_eq_iff in H3;
    try rewrite PeanoNat.Nat.compare_lt_iff in H1;
    try rewrite PeanoNat.Nat.compare_lt_iff in H2;
    try rewrite PeanoNat.Nat.compare_lt_iff in H3;
    try rewrite PeanoNat.Nat.compare_gt_iff in H1;
    try rewrite PeanoNat.Nat.compare_gt_iff in H2;
    try rewrite PeanoNat.Nat.compare_gt_iff in H3;
    destruct n;
    try lia.
  --- rewrite H2.
      rewrite H3.
      simpl.
      rewrite PeanoNat.Nat.compare_refl.
      reflexivity.
  --- rewrite H2.
      rewrite <- H3.
      destruct (PeanoNat.Nat.leb) eqn:Habs;
      try (move/ PeanoNat.Nat.leb_spec0 in Habs;
      lia).
      simpl.
      rewrite PeanoNat.Nat.compare_refl.
      reflexivity.
  --- rewrite H1.
      simpl.
      rewrite PeanoNat.Nat.lt_succ_r in H3.
      move/ PeanoNat.Nat.leb_spec0 in H3.
      rewrite H3.
      simpl.
      have Hlt : n' < S (S n).
      lia.
      rewrite <- PeanoNat.Nat.compare_lt_iff in Hlt.
      rewrite Hlt.
      reflexivity.
  --- simpl.
      rewrite (Compare_dec.leb_correct_conv _ _ H3).
      rewrite <- PeanoNat.Nat.compare_gt_iff in H2.
      rewrite H2.
      reflexivity.
  --- simpl. 
      rewrite (Compare_dec.leb_correct_conv _ _ H3).
      rewrite (Compare_dec.leb_correct_conv _ _).
      lia.
      simpl.
      rewrite <- PeanoNat.Nat.compare_gt_iff in H2.
      rewrite H2.
      reflexivity.
  --- simpl.
      rewrite <- PeanoNat.Nat.compare_eq_iff in H2.
      rewrite H2.
      reflexivity.
  --- rewrite (Compare_dec.leb_correct_conv _ _).
      lia.
      simpl.
      rewrite <- PeanoNat.Nat.compare_eq_iff in H2.
      rewrite H2.
      reflexivity.
  --- simpl.
      rewrite (Compare_dec.leb_correct_conv _ _).
      lia.
      simpl.
      rewrite <- PeanoNat.Nat.compare_lt_iff in H2.
      rewrite H2.
      reflexivity.
  --- simpl.
      rewrite (Compare_dec.leb_correct_conv _ _).
      lia.
      simpl.
      rewrite <- PeanoNat.Nat.compare_lt_iff in H2.
      rewrite H2.
      reflexivity.
  --- simpl.
      rewrite (Compare_dec.leb_correct _ _).
      lia.
      simpl.
      have Hlt : m' < S (S n).
      lia.
      rewrite <- PeanoNat.Nat.compare_lt_iff in Hlt.
      rewrite Hlt.
      reflexivity.
  --- simpl.
      rewrite (Compare_dec.leb_correct_conv _ _).
      lia.
      rewrite <- PeanoNat.Nat.compare_gt_iff in H2.
      rewrite H2.
      reflexivity.
  --- simpl.
      rewrite (Compare_dec.leb_correct_conv _ _).
      auto.
      rewrite (Compare_dec.leb_correct_conv _ _).
      lia.
      simpl.
      rewrite <- PeanoNat.Nat.compare_gt_iff in H2.
      rewrite H2.
      reflexivity.
  - simpl.
    rewrite bshift_bshift.
    lia.
    f_equal.
    apply IHe.
    lia.
  - simpl.
    f_equal;
    eauto.
  - simpl.
    f_equal;
    eauto.
  - simpl.
    f_equal;
    eauto.
  - simpl.
    f_equal;
    eauto.
Qed.

Lemma bshift_bsubst' {e f : termT} {m n : nat} :
    m <= n -> bshift m (e[n <- f]) = (bshift m e) [S n <- bshift m f].
Proof.
  move: f m n.
  induction e;
  move=> f' m' n' Hle;
  eauto; simpl;
  try (f_equal;
    auto).
  - destruct (PeanoNat.Nat.compare m' n) eqn:H1;
    destruct (PeanoNat.Nat.compare n' n) eqn:H2;
    try rewrite PeanoNat.Nat.compare_eq_iff in H1;
    try rewrite PeanoNat.Nat.compare_eq_iff in H2;
    try rewrite PeanoNat.Nat.compare_lt_iff in H1;
    try rewrite PeanoNat.Nat.compare_lt_iff in H2;
    try rewrite PeanoNat.Nat.compare_gt_iff in H1;
    try rewrite PeanoNat.Nat.compare_gt_iff in H2;
    try lia.
  --- move/ PeanoNat.Nat.leb_spec0 in Hle.
      rewrite H2 in Hle.
      rewrite Hle.
      simpl.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2;
      auto.
  --- rewrite H1.
      rewrite PeanoNat.Nat.leb_refl.
      simpl.  
      rewrite PeanoNat.Nat.leb_refl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2;
      auto.
  --- rewrite Compare_dec.leb_correct.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2;
      auto.
  --- destruct n.
  ----- lia.
  ----- simpl.
        rewrite Compare_dec.leb_correct.
        lia.
        rewrite Compare_dec.leb_correct.
        lia.
        simpl.
        rewrite (PeanoNat.Nat.compare_lt_iff _ _).2;
        auto.
  --- simpl.
      rewrite Compare_dec.leb_correct.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2;
      auto.
  --- simpl.
      rewrite Compare_dec.leb_correct_conv.
      lia.
      simpl.
      destruct n.
  ----- reflexivity.
  ----- rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
        lia.
        reflexivity.
  - f_equal.
    rewrite bshift_bshift.
    lia.
    apply IHe.
    lia.
Qed.

Lemma bsubst_bsubst {e f g : termT} {m n : nat} :
    m <= n -> e[m <- f][n <- g] = e[S n <- bshift m g][m <- f[n <- g]].
Proof.
  move: m n f g.
  induction e;
  move=> m' n' f' g' Hle;
  eauto;
  [ | | simpl; f_equal; auto ..].
  - destruct (PeanoNat.Nat.compare m' n) eqn:H1;
    destruct (PeanoNat.Nat.compare (S n') n) eqn:H2;
    try rewrite PeanoNat.Nat.compare_eq_iff in H1;
    try rewrite PeanoNat.Nat.compare_eq_iff in H2;
    try rewrite PeanoNat.Nat.compare_lt_iff in H1;
    try rewrite PeanoNat.Nat.compare_lt_iff in H2;
    try rewrite PeanoNat.Nat.compare_gt_iff in H1;
    try rewrite PeanoNat.Nat.compare_gt_iff in H2;
    destruct n;
    try lia;
    simpl.
  --- rewrite (PeanoNat.Nat.compare_eq_iff _ _).2.
      assumption.
      reflexivity.
  --- rewrite (PeanoNat.Nat.compare_gt_iff n' _).2.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2;
      auto.
  --- rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      assumption.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2.
      lia.
      simpl.
      rewrite bshift_bsubst_eq.
      reflexivity.
  --- rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      assumption.
      simpl.
      rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      lia.
      destruct n;
      simpl.
  ------ lia.
  ------ rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
         lia.
         reflexivity.
  --- rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      assumption.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      assumption.
      reflexivity.
  --- rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      assumption.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      lia.
      reflexivity.
  --- rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      assumption.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      lia.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      assumption.
      reflexivity.
  - simpl.
    f_equal.
    rewrite bshift_bshift.
    lia.
    rewrite (@bshift_bsubst');
    try apply IHe;
    lia.
Qed.