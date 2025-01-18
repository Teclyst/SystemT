Require Import Definitions.Ident.
Require Import Definitions.Term.
Require Import Definitions.Type.
Require Import Theorems.Substitution.
Require Import Definitions.Reduction.

Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import Init.Wf.
Require Import Lia.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

Lemma one_reduction_reduction_1 {e f : termT} :
    (e ->1 f) <-> (e ->(1) f).
Proof.
  constructor.
  - eauto using reduction.
  - intro Hred.
    inversion Hred.
    inversion H1.
    rewrite H6 in H0.
    exact H0.
Qed.

Lemma one_reduction_reduction_star {e f : termT} :
    (e ->1 f) -> (e ->* f).
Proof.
  exists 1.
  rewrite <- one_reduction_reduction_1.
  assumption.
Qed.

Lemma reduction_trans {m n : nat} {e f g : termT} :
    (e ->(m) f) -> (f ->(n) g) -> (e ->(m + n) g).
Proof.
  move: e f g.
  induction m;
  move=> e f g Hm Hn;
  simpl.
  - inversion Hm.
    exact Hn.
  - inversion Hm.
    eapply red_next.
  --- exact H0.
  --- eapply IHm.
  ----- exact H1.
  ----- auto.
Qed.

Lemma reduction_one_reduction {n : nat} {e f g : termT} :
    (e ->(n) f) -> (f ->1 g) -> (e ->(S n) g).
Proof.
  rewrite one_reduction_reduction_1.
  rewrite <- (Nat.add_1_r n).
  exact reduction_trans.
Qed.

#[export] Instance preorder_reduction_star :
    RelationClasses.PreOrder reduction_star.
Proof.
  constructor.
  - intro e.
    exists O.
    exact (red_refl_zero _).
  - intros e f g Hred1 Hred2. 
    destruct Hred1 as [m Hredm].
    destruct Hred2 as [n Hredn].
    exists (m + n).
    exact (reduction_trans Hredm Hredn).
Qed.

Lemma red_star_next {e f g : termT} :
    (e ->1 f) -> (f ->* g) -> (e ->* g).
Proof.
  transitivity f;
  auto using one_reduction_reduction_star.
Qed.

#[export] Instance equivalence_equivalence :
    RelationClasses.Equivalence equivalence.
Proof.
  constructor.
  - intro e.
    apply red_eq_red.
    reflexivity.
  - eauto using equivalence.
  - eauto using equivalence.
Qed.

Lemma reduction_absT {e f : termT} {n : nat} :
    (e ->(n) f) -> (absT e ->(n) absT f).
Proof.
  intro Hred.
  induction Hred.
  - eauto using reduction.
  - apply redind_absT in H.
    eauto using reduction.
Qed.

Lemma reduction_appT {e f g h : termT} {m n : nat} :
    (e ->(m) g) -> (f ->(n) h) -> (appT e f ->(m + n) appT g h).
Proof.
  intro Hred1.
  move: f h.
  induction Hred1; simpl; move=> f' h' Hred2.
  - move: e.
    induction Hred2.
  --- eauto using reduction.
  --- intro h.
      apply (redind_appT_r h) in H.
      eauto using reduction. 
  - apply (redind_appT_l _ _ f') in H.
    eauto using reduction.
Qed.

Lemma reduction_iteT {e f g h i j : termT} {m n o : nat} :
    (e ->(m) h) -> (f ->(n) i) -> (g ->(o) j) ->
    (iteT e f g ->(m + n + o) iteT h i j).
Proof.
  move=> Hred1.
  move: f g i j.
  induction Hred1;
  simpl;
  move=> f' g' i' j' Hred2.
  - move: e g' j'.
    induction Hred2;
    move=> e' g' j' Hred3.
  --- move: e e'.
      induction Hred3.
  ----- eauto using reduction.
  ----- move=> h i.
        apply (redind_iteT_r i h) in H.
        eauto using reduction. 
  --- apply (redind_iteT_c e' _ _  g') in H.
      eauto using reduction. 
  - apply (redind_iteT_l _ _ f' g') in H.
    intro Hred3.
    eauto using reduction.
Qed.

Lemma reduction_sT {e f : termT} {n : nat} :
    (e ->(n) f) -> (sT e ->(n) sT f).
Proof.
  intro Hred.
  induction Hred.
  - eauto using reduction.
  - apply redind_sT in H.
    eauto using reduction.
Qed.

Lemma reduction_recT {e f g h i j : termT} {m n o : nat} :
    (e ->(m) h) -> (f ->(n) i) -> (g ->(o) j) ->
    (recT e f g ->(m + n + o) recT h i j).
Proof.
  move=> Hred1.
  move: f g i j.
  induction Hred1;
  simpl;
  move=> f' g' i' j' Hred2.
  - move: e g' j'.
    induction Hred2;
    move=> e' g' j' Hred3.
  --- move: e e'.
      induction Hred3.
  ----- eauto using reduction.
  ----- move=> h i.
        apply (redind_recT_r i h) in H.
        eauto using reduction. 
  --- apply (redind_recT_c e' _ _  g') in H.
      eauto using reduction. 
  - apply (redind_recT_l _ _ f' g') in H.
    intro Hred3.
    eauto using reduction.
Qed.

Lemma reduction_star_absT {e f : termT} :
    (e ->* f) -> (absT e ->* absT f).
Proof.
  intro Hred.
  destruct Hred as [m Hm].
  exists m.
  eauto using reduction_absT.
Qed.

Lemma reduction_star_appT {e f g h : termT} :
    (e ->* g) -> (f ->* h) -> (appT e f ->* appT g h).
Proof.
  intros Hred1 Hred2.
  destruct Hred1 as [o Ho].
  destruct Hred2 as [p Hp].
  exists (o + p).
  eauto using reduction_appT.
Qed.

Lemma reduction_star_iteT {e f g h i j : termT} :
    (e ->* h) -> (f ->* i) -> (g ->* j) -> (iteT e f g ->* iteT h i j).
Proof.
  intros Hred1 Hred2 Hred3.
  destruct Hred1 as [o Ho].
  destruct Hred2 as [p Hp].
  destruct Hred3 as [q Hq].
  exists (o + p + q).
  eauto using reduction_iteT.
Qed.

Lemma reduction_star_sT {e f : termT} :
    (e ->* f) -> (sT e ->* sT f).
Proof.
  intro Hred.
  destruct Hred as [m Hm].
  exists m.
  eauto using reduction_sT.
Qed.

Lemma reduction_star_recT {e f g h i j : termT} :
    (e ->* h) -> (f ->* i) -> (g ->* j) ->
    (recT e f g ->* recT h i j).
Proof.
  intros Hred1 Hred2 Hred3.
  destruct Hred1 as [o Ho].
  destruct Hred2 as [p Hp].
  destruct Hred3 as [q Hq].
  exists (o + p + q).
  eauto using reduction_recT.
Qed.

Hint Resolve
  one_reduction_reduction_star
  reduction_star_absT
  reduction_star_appT
  reduction_star_iteT
  reduction_star_sT
  reduction_star_recT : reduction_star_lemmas.

Lemma one_reduction_bsubst_l {e f g : termT} {n : nat} :
    (e ->1 f) -> (e[n <- g] ->1 f[n <- g]).
Proof.
  move=> Hred.
  move: g n.
  induction Hred;
  move=> g' n;
  eauto using one_reduction.
  - rewrite bsubst_bsubst.
    lia.
    apply redex_beta.
  - simpl.
    eauto using one_reduction.
Qed.

Lemma bshift_one_reduction {e f: termT} {n : nat} :
    (e ->1 f) -> (bshift n e ->1 bshift n f).
Proof.
  move => Hred.
  move: n.
  induction Hred;
  move=> n;
  simpl;
  eauto using one_reduction.
  rewrite bshift_bsubst.
  lia.
  eauto using one_reduction.
Qed.

Lemma reduction_bsubst_l {e f g : termT} {m n : nat} :
    (e ->(m) f) -> (e[n <- g] ->(m) f[n <- g]).
Proof.
  move=> Hred.
  move: g n.
  induction Hred;
  move=> g' n';
  eauto using reduction, one_reduction_bsubst_l.
Qed.

Lemma reduction_star_bsubst_l {e f g : termT} {n : nat} :
    (e ->* f) -> (e[n <- g] ->* f[n <- g]).
Proof.
  move=> Hred.
  destruct Hred as [m Hred].
  exists m.
  apply reduction_bsubst_l.
  assumption.
Qed.

Lemma one_reduction_bsubst_r {e f g : termT} {n : nat} :
    (f ->1 g) -> (e[n <- f] ->* e[n <- g]).
Proof.
  move: f g n.
  induction e;
  move => f' g' m Hred;
  simpl;
  eauto with reduction_star_lemmas;
  try reflexivity.
  - simpl.
    destruct (PeanoNat.Nat.compare m n); try reflexivity.
    eauto with reduction_star_lemmas.
  - apply reduction_star_absT.
    apply IHe.
    apply bshift_one_reduction.
    assumption.
Qed.

Lemma reduction_bsubst_r {e f g : termT} {m n : nat} :
    (f ->(m) g) -> (e[n <- f] ->* e[n <- g]).
Proof.
  move=> Hred.
  move: e n.
  induction Hred;
  move=> e' n'.
  - reflexivity.
  - transitivity (e'[n' <- f]).
  --- apply one_reduction_bsubst_r.
      assumption.
  --- auto.
Qed.

Lemma reduction_star_bsubst_r {e f g : termT} {n : nat} :
    (f ->* g) -> (e[n <- f] ->* e[n <- g]).
Proof.
  move=> Hred.
  destruct Hred as [m Hred].
  eapply reduction_bsubst_r.
  exact Hred.
Qed.

Lemma reduction_star_bsubst {e f g h : termT} {n : nat} :
    (e ->* g) -> (f ->* h) -> (e[n <- f] ->* g[n <- h]).
Proof.
  intros Hredl Hredr.
  transitivity (g[n <-f]);
  eauto using reduction_star_bsubst_l, reduction_star_bsubst_r.
Qed.

Hint Resolve
  reduction_star_bsubst : reduction_star_lemmas.

Lemma reducibleb_spec :
    forall e : termT, Bool.reflect (reducible e) (reducibleb e).
Proof.
  intro e.
  induction e.
  - right.
    intro H.
    inversion H.
    inversion H0.
  - right.
    intro H.
    inversion H.
    inversion H0.
  - simpl.
    inversion IHe.
  --- left.
      destruct H0 as [f Hred].
      exists (absT f).
      auto using one_reduction.
  --- right.
      intro Hredible.
      destruct Hredible as [f Hred].
      inversion Hred.
      apply H0.
      exists f0.
      auto.
  - inversion IHe1.
  --- simpl.
      rewrite <- H.
      simpl.
      destruct e1;
      left;
      destruct H0 as [g Hred];
      eexists;
      eauto using one_reduction.
  --- inversion IHe2.
  ----- simpl.
        rewrite <- H1.
        rewrite <- H.
        simpl.
        destruct e1 eqn:Heq;
        left;
        destruct H2 as [g Hred];
        rewrite <- Heq;
        eexists;
        eauto using one_reduction.
  ----- simpl.
        destruct e1 eqn:Heq; [
        | |
        left;
        exists (t[O <- e2]);
        eauto using one_reduction |
        ..
        ];
      rewrite <- H1;
      rewrite <- H;
      simpl;
      right;
      try (intro Hredible;
      destruct Hredible as [g Hred];
      inversion Hred; [
        apply H0;
        eexists;
        eauto using one_reduction |
        apply H2;
        eexists;
        eauto using one_reduction
      ]).
  - right.
    intro H.
    destruct H as [g Hred].
    inversion Hred.
  - right.
    intro H.
    destruct H as [g Hred].
    inversion Hred.
  - simpl.
    inversion IHe1;
    inversion IHe2;
    inversion IHe3;
    simpl;
    try (
      destruct e1;
      left;
      try destruct H0 as [f1 Hred1];
      try destruct H2 as [f2 Hred2];
      try destruct H4 as [f3 Hred3];
      eexists;
      eauto using one_reduction
    ).
    destruct e1;
    try (
      right;
      intro Habs;
      destruct Habs as [g Hred];
      inversion Hred;
      try (
        apply H0;
        eexists;
        eauto;
        fail
      );
      try (
        apply H2;
        eexists;
        eauto;
        fail
      );
      try (
        apply H4;
        eexists;
        eauto;
        fail
      )
    );
    left;
    eexists;
    eauto using one_reduction.
  - simpl.
    right.
    intro Habs.
    destruct Habs as [e Habs].
    inversion Habs.
  - simpl.
    inversion IHe.
  --- left.
      destruct H0 as [f Hred].
      eexists.
      eauto using one_reduction.
  --- right.
      intro Habs.
      destruct Habs as [f Habs].
      inversion Habs.
      apply H0.
      eexists.
      eauto using one_reduction.
  - simpl.
    inversion IHe1;
    inversion IHe2;
    inversion IHe3;
    simpl;
    try (
      destruct e3;
      left;
      try destruct H0 as [f1 Hred1];
      try destruct H2 as [f2 Hred2];
      try destruct H4 as [f3 Hred3];
      eexists;
      eauto using one_reduction
    ).
    destruct e3;
    try (
      right;
      intro Habs;
      destruct Habs as [g Hred];
      inversion Hred;
      try (
        apply H0;
        eexists;
        eauto;
        fail
      );
      try (
        apply H2;
        eexists;
        eauto;
        fail
      );
      try (
        apply H4;
        eexists;
        eauto;
        fail
      )
    );
    left;
    eexists;
    eauto using one_reduction.
Qed.

Lemma reducible_or_normal_form {e : termT} : {reducible e} + {normal_form e}.
Proof.
  destruct (reducibleb e) eqn:Heq;
  move/ reducibleb_spec in Heq.
  - left.
    assumption.
  - right.
    assumption.
Qed.

Lemma left_reduce_spec {e f : termT} :
    left_reduce e = Some f -> (e ->1 f).
Proof.
  move: f.
  induction e;
  simpl;
  move=> g Heq;
  try discriminate Heq.
  - destruct (left_reduce e) as [f | ];
    try discriminate Heq.
    simpl in Heq.
    inversion Heq.
    eauto using one_reduction.
Admitted.

Lemma left_reduce_reducible {e : termT} :
    reducible e -> exists f : termT, left_reduce e = Some f.
Admitted.

Lemma one_reduction_par_fsubst {e f : termT} {s : FMap.t termT} :
    (e ->1 f) -> (par_fsubst s e ->1 par_fsubst s f).
Proof.
  move=> Hred.
  move: s.
  induction Hred;
  simpl;
  eauto using one_reduction.
  move=> s.
  rewrite <- par_fsubst_bsubst.
  exact (redex_beta _ _).
Qed.
