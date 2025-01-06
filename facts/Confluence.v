Require Import Terms.
Require Import Reduction.
Require Import Lia.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.

Inductive par_one_reduction : termT -> termT -> Prop :=
  | par_redrefl : forall e : termT, par_one_reduction e e
  | par_redex_beta : forall e f g h : termT,
    par_one_reduction e g -> par_one_reduction f h ->
    par_one_reduction (appT (absT e) f) (g[O <- h])
  | par_redex_iteT_trueT :
    forall e f g : termT,
    par_one_reduction e g ->
    par_one_reduction (iteT trueT e f) g
  | par_redex_iteT_falseT :
    forall e f g : termT,
    par_one_reduction f g ->
    par_one_reduction (iteT falseT e f) g
  | par_redex_recT_oT :
    forall e f g : termT,
    par_one_reduction e g ->
    par_one_reduction (recT e f oT) g
  | par_redex_recT_sT :
    forall e f g h i j : termT,
    par_one_reduction e h ->
    par_one_reduction f i ->
    par_one_reduction g j ->
    par_one_reduction (recT e f (sT g)) (appT (appT i (recT h i j)) j)
  | par_redind_absT :
    forall e f : termT,
    par_one_reduction e f ->
    par_one_reduction (absT e) (absT f)
  | par_redind_appT :
    forall e f g h : termT,
    par_one_reduction e g ->
    par_one_reduction f h ->
    par_one_reduction (appT e f) (appT g h)
  | par_redind_iteT :
    forall e f g h i j : termT,
    par_one_reduction e h ->
    par_one_reduction f i ->
    par_one_reduction g j ->
    par_one_reduction (iteT e f g) (iteT h i j)
  | redind_sT :
    forall e f : termT,
    par_one_reduction e f ->
    par_one_reduction (sT e) (sT f)
  | par_redind_recT :
    forall e f g h i j : termT,
    par_one_reduction e h ->
    par_one_reduction f i ->
    par_one_reduction g j ->
    par_one_reduction (recT e f g) (recT h i j).

Notation "e =>1 f" := (par_one_reduction e f) (at level 80).

Inductive par_reduction : nat -> termT -> termT -> Prop :=
  | par_red_refl_zero : forall e : termT, par_reduction O e e
  | par_red_next :
    forall n : nat, forall e f g : termT,
    (e =>1 f) -> par_reduction n f g -> 
    par_reduction (S n) e g.

Notation "e =>( n ) f" := (par_reduction n e f) (at level 80).

Definition par_reduction_star (e f : termT) : Prop :=
    exists n : nat, e =>(n) f.

Notation "e =>* f" := (par_reduction_star e f) (at level 80).

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

Lemma bshift_subst {e f : termT} {m n : nat} :
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

Lemma parallel_subst_bshift {e f : termT} {n : nat} :
  e =>1 f -> bshift n e =>1 bshift n f.
Proof.
  move => Hred1.
  move: n.
  induction Hred1;
  move=> n;
  eauto using par_one_reduction.
  - simpl.
    rewrite bshift_subst.
    lia.
    eapply par_redex_beta;
    eauto.
  - apply par_redex_recT_sT;
    fold bshift;
    eauto.
Qed.

Axiom FILL : forall P : Prop, P.

Lemma parallel_subst {e f g h : termT} {n : nat} :
    e =>1 g -> f =>1 h -> e[n <- f] =>1 g[n <- h].
Proof.
  intro Hred1.
  move: n f h.
  induction Hred1;
  eauto using par_one_reduction.
  - induction e;
    move=> n' f' h' Hred2;
    simpl;
    eauto using par_one_reduction.
  --- destruct PeanoNat.Nat.compare;
      eauto using par_one_reduction.
  --- apply par_redind_absT.
      apply IHe.
      exact (parallel_subst_bshift Hred2).
  - move=> n' f' h' Hred2;
    simpl.
    apply FILL. (* TODO. *)
  - move=> n' f' h' Hred2.
    apply par_redex_recT_sT;
    fold bsubst;
    auto.
  - move=> n' f' h' Hred2.
    apply par_redind_absT;
    fold bsubst;
    apply IHHred1.
    apply parallel_subst_bshift.
    exact Hred2.
Qed.

Lemma parallel_subst_confluence {e f g : termT} :
  (e =>1 f) -> (e =>1 g) ->
  exists h : termT,
  (f =>1 h) /\ (g =>1 h).
Proof.
  move=> Hred1.
  move: g.
  induction Hred1;
  move=> g' Hred2.
  - eexists.
    eauto using par_one_reduction.
  - inversion Hred2.
  --- exists (g[O <- h]).
      eauto using par_one_reduction.
  --- destruct (IHHred1_1 g0) as [i Hi].
      auto.
      destruct (IHHred1_2 h0) as [j Hj].
      auto.
      exists (i[O <- j]).
      destruct Hi.
      destruct Hj.
      constructor;
      apply parallel_subst;
      auto.
  --- inversion H1;
      destruct (IHHred1_2 h0) as [i Hi];
      auto;
      destruct Hi.
  ----- exists (g[O <- i]).
        eauto using par_one_reduction, parallel_subst.
  ----- destruct (IHHred1_1 f1) as [j Hj];
        auto;
        destruct Hj.
        exists (j[O <- i]);
        eauto using par_one_reduction, parallel_subst.
  - inversion Hred2.
    eauto using par_one_reduction.
  --- apply IHHred1.
      exact H2.
  --- destruct (IHHred1 i H4).
      inversion H2.
      destruct H6.
      eauto using par_one_reduction.
  - inversion Hred2.
    eauto using par_one_reduction.
  --- apply IHHred1.
      exact H2.
  --- destruct (IHHred1 j H5).
      inversion H2.
      destruct H6.
      eauto using par_one_reduction.
  - inversion Hred2.
  --- eauto using par_one_reduction.
  --- apply IHHred1.
      exact H2.
  --- inversion H5. 
      destruct (IHHred1 h H2).
      destruct H8.
      eauto using par_one_reduction.
  - inversion Hred2.
  --- eauto using par_one_reduction.
  --- destruct (IHHred1_1 h0 H2) as [k Hk].
      destruct (IHHred1_2 i0 H4) as [l Hl].
      destruct (IHHred1_3 j0 H5) as [m Hm].
      destruct Hk.
      destruct Hl.
      destruct Hm.
      exists (appT (appT l (recT k l m)) m).
      eauto 8 using par_one_reduction.
  --- inversion H5;
      destruct (IHHred1_1 h0 H2) as [k Hk];
      destruct (IHHred1_2 i0 H4) as [l Hl];
      destruct Hk;
      destruct Hl;
      eauto 7 using par_one_reduction.
      destruct (IHHred1_3 f1 H7) as [m Hm].
      destruct Hm.
      exists (appT (appT l (recT k l m)) m).
      eauto 6 using par_one_reduction.
  - inversion Hred2.
  --- eauto using par_one_reduction.
  --- destruct (IHHred1 f0 H0) as [h Hh].
      exists (absT h).
      destruct Hh.
      eauto using par_one_reduction.
  - inversion Hred2.
  --- eauto using par_one_reduction.
  --- rewrite <- H in Hred1_1.
      inversion Hred1_1;
      destruct (IHHred1_2 h0 H3) as [i Hi];
      destruct Hi.
  ----- exists (g0[0 <- i]).
        eauto using par_one_reduction, parallel_subst.
  ----- destruct (IHHred1_1 (absT g0)) as [j Hj].
        rewrite <- H.
        eauto using par_one_reduction.
        destruct Hj.
        rewrite <- H6 in H9.
        inversion H9.
  ------- rewrite <- H12 in H10.
          inversion H10;
          eauto using par_one_reduction, parallel_subst.
  ------- rewrite <- H13 in H10.
          inversion H10;
          eauto using par_one_reduction, parallel_subst.
  --- destruct (IHHred1_1 g0 H1) as [k Hk].
      destruct (IHHred1_2 h0 H3) as [l Hl].
      destruct Hk.
      destruct Hl.
      eauto using par_one_reduction.
  - inversion Hred2.
  --- eauto using par_one_reduction.
  --- destruct (IHHred1_2 g' H3) as [k Hk].
      destruct Hk.
      rewrite <- H in Hred1_1.
      inversion Hred1_1.
      eauto using par_one_reduction.
  --- destruct (IHHred1_3 g' H3) as [k Hk].
      destruct Hk.
      rewrite <- H in Hred1_1.
      inversion Hred1_1.
      eauto using par_one_reduction.
  --- destruct (IHHred1_1 h0 H2) as [k Hk].
      destruct (IHHred1_2 i0 H4) as [l Hl].
      destruct (IHHred1_3 j0 H5) as [m Hm].
      destruct Hk.
      destruct Hl.
      destruct Hm.
      eauto using par_one_reduction.
  - inversion Hred2.
  --- eauto using par_one_reduction.
  --- destruct (IHHred1 f0 H0) as [k Hk].
      destruct Hk.
      eauto using par_one_reduction.
  - inversion Hred2.
  --- eauto using par_one_reduction.
  --- rewrite <- H2 in Hred1_3.
      inversion Hred1_3. 
      destruct (IHHred1_1 g' H3) as [k Hk].
      destruct Hk.
      eauto using par_one_reduction.
  --- rewrite <- H1 in Hred1_3.
      inversion Hred1_3.
  ----- destruct (IHHred1_1 h0 H2) as [k Hk].
        destruct (IHHred1_2 i0 H4) as [l Hl].
        destruct (IHHred1_3 (sT j0)) as [m Hm].
        rewrite <- H1.
        eauto using par_one_reduction.
        destruct Hk.
        destruct Hl.
        destruct Hm.
        eauto 7 using par_one_reduction.
  ----- destruct (IHHred1_1 h0 H2) as [k Hk].
        destruct (IHHred1_2 i0 H4) as [l Hl].
        destruct (IHHred1_3 (sT j0)) as [m Hm].
        rewrite <- H1.
        eauto using par_one_reduction.
        destruct Hk.
        destruct Hl.
        destruct Hm.
        rewrite <- H8 in H13.
        inversion H13.
  ------- rewrite <- H16 in H14.
          inversion H14;
          eauto 7 using par_one_reduction.
  ------- rewrite <- H17 in H14.
          inversion H14;
          eauto 7 using par_one_reduction.
  --- destruct (IHHred1_1 h0 H2) as [k Hk].
      destruct (IHHred1_2 i0 H4) as [l Hl].
      destruct (IHHred1_3 j0 H5) as [m Hm].
      destruct Hk.
      destruct Hl.
      destruct Hm.
      eauto using par_one_reduction.
Qed.

Theorem confluence {e f g : termT} :
  (e ->* f) -> (e ->* g) ->
  exists h : termT,
  (f ->* h) /\ (g ->* h).
Proof.
Admitted.