Require Import Definitions.Term.
Require Import Definitions.Reduction.
Require Import Theorems.Reduction.
Require Import Theorems.Substitution.
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

Lemma parallel_bsubst_bshift {e f : termT} {n : nat} :
  e =>1 f -> bshift n e =>1 bshift n f.
Proof.
  move => Hred1.
  move: n.
  induction Hred1;
  move=> n;
  eauto using par_one_reduction.
  - simpl.
    rewrite bshift_bsubst.
    lia.
    eapply par_redex_beta;
    eauto.
  - apply par_redex_recT_sT;
    fold bshift;
    eauto.
Qed.

Lemma parallel_bsubst {e f g h : termT} {n : nat} :
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
      exact (parallel_bsubst_bshift Hred2).
  - move=> n' f' h' Hred2;
    simpl.
    rewrite bsubst_bsubst.
    lia.
    apply par_redex_beta.
  --- apply IHHred1_1.
      eauto using parallel_bsubst_bshift.
  --- apply IHHred1_2.
      assumption.
  - move=> n' f' h' Hred2.
    apply par_redex_recT_sT;
    fold bsubst;
    auto.
  - move=> n' f' h' Hred2.
    apply par_redind_absT;
    fold bsubst;
    apply IHHred1.
    apply parallel_bsubst_bshift.
    exact Hred2.
Qed.

Lemma par_one_reduction_confluence {e f g : termT} :
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
      apply parallel_bsubst;
      auto.
  --- inversion H1;
      destruct (IHHred1_2 h0) as [i Hi];
      auto;
      destruct Hi.
  ----- exists (g[O <- i]).
        eauto using par_one_reduction, parallel_bsubst.
  ----- destruct (IHHred1_1 f1) as [j Hj];
        auto;
        destruct Hj.
        exists (j[O <- i]);
        eauto using par_one_reduction, parallel_bsubst.
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
        eauto using par_one_reduction, parallel_bsubst.
  ----- destruct (IHHred1_1 (absT g0)) as [j Hj].
        rewrite <- H.
        eauto using par_one_reduction.
        destruct Hj.
        rewrite <- H6 in H9.
        inversion H9.
  ------- rewrite <- H12 in H10.
          inversion H10;
          eauto using par_one_reduction, parallel_bsubst.
  ------- rewrite <- H13 in H10.
          inversion H10;
          eauto using par_one_reduction, parallel_bsubst.
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

Lemma par_reduction_confluence_aux {e f g : termT} {n : nat} :
  (e =>1 f) -> (e =>(n) g) ->
  exists h : termT,
  (f =>(n) h) /\ (g =>1 h).
Proof.
  move=> Hred1 Hred2.
  move:f Hred1.
  induction Hred2;
  move=> h Hred1.
  - exists h.
    eauto using par_reduction.
  - destruct (par_one_reduction_confluence H Hred1) as [i Hi].
    destruct Hi as [Hfi Hhi].
    destruct (IHHred2 _ Hfi) as [j Hj].
    destruct Hj.
    eauto using par_reduction.
Qed.

Lemma par_reduction_confluence {e f g : termT} {m n : nat} :
    (e =>(m) f) -> (e =>(n) g) ->
    exists h : termT,
    (f =>(n) h) /\ (g =>(m) h).
Proof.
  move=> Hred1.
  move:g n.
  induction Hred1;
  move=> h m Hred2.
  - exists h.
    eauto using par_reduction.
  - destruct (par_reduction_confluence_aux H Hred2) as [i Hi].
    destruct Hi.
    destruct (IHHred1 _ _ H0) as [j Hj].
    destruct Hj.
    eauto using par_reduction.
Qed.

Lemma one_reduction_par_one_reduction {e f : termT} :
    (e ->1 f) -> (e =>1 f).
Proof.
  intro Hred1.
  induction Hred1;
  eauto using par_one_reduction.
Qed.

Lemma reduction_par_reduction {e f : termT} {n : nat} :
    (e ->(n) f) -> (e =>(n) f).
Proof.
  intro Hred.
  induction Hred;
  eauto using par_reduction, one_reduction_par_one_reduction.
Qed.

Lemma par_one_reduction_reduction_star {e f : termT} :
    (e =>1 f) -> (e ->* f).
Proof.
  intro Hred.
  induction Hred;
  (try eauto with reduction_star_lemmas).
  - reflexivity.
  - transitivity (e[O <- f]).
  --- exists 1.
      rewrite <- one_reduction_reduction_1.
      eauto using one_reduction.
  --- apply reduction_star_bsubst;
      assumption.
  - transitivity e.
  --- exists 1.
      rewrite <- one_reduction_reduction_1.
      eauto using one_reduction.
  --- assumption.
  - transitivity f.
  --- exists 1.
      rewrite <- one_reduction_reduction_1.
      eauto using one_reduction.
  --- assumption.
  - transitivity e.
  --- exists 1.
      rewrite <- one_reduction_reduction_1.
      eauto using one_reduction.
  --- assumption.
  - transitivity (appT (appT f (recT e f g)) g).
  --- exists 1.
      rewrite <- one_reduction_reduction_1.
      eauto using one_reduction.
  --- eauto with reduction_star_lemmas.
Qed. 

Lemma par_reduction_reduction_star {e f : termT} {n : nat} :
    (e =>(n) f) -> (e ->* f).
Proof.
  intro Hred.
  induction Hred.
  - reflexivity.
  - apply par_one_reduction_reduction_star in H.
    transitivity f;
    assumption.
Qed.

Theorem confluence {e f g : termT} :
    (e ->* f) -> (e ->* g) ->
    exists h : termT,
    f ->* h /\ g ->* h.
Proof.
  intros Hred1 Hred2.
  destruct Hred1 as [m Hred1].
  destruct Hred2 as [n Hred2].
  apply reduction_par_reduction in Hred1.
  apply reduction_par_reduction in Hred2.
  destruct (par_reduction_confluence Hred1 Hred2) as [h [Hred3 Hred4]].
  apply par_reduction_reduction_star in Hred3.
  apply par_reduction_reduction_star in Hred4.
  eauto using par_one_reduction_reduction_star.
Qed.

Lemma equivalence_reduction_star {e f : termT} :
    e === f <-> exists g : termT, e ->* g /\ f ->* g.
Proof.
  constructor.
  - intro Hequiv.
    induction Hequiv.
  --- exists f.
      constructor;
      auto;
      reflexivity.
  --- destruct IHHequiv as [g [He Hf]].
      eauto.
  --- destruct IHHequiv1 as [h [Heh Hfh]].
      destruct IHHequiv2 as [i [Hfi Hgi]].
      destruct (confluence (e := f) (f := h) (g := i)) as [j [Hhj Hgj]];
      try assumption.
      exists j.
      constructor.
  ----- transitivity h;
        assumption.
  ----- transitivity i;
        assumption.
  - intro Hred.
    destruct Hred as [g [Hrede Hredf]].
    eauto using equivalence. 
Qed.
