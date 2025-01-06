Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import Ident.
Require Import Terms.
Require Import Init.Wf.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.

Inductive one_reduction : termT -> termT -> Prop :=
  | redex_beta :
    forall e f : termT,
    one_reduction (appT (absT e) f) (e[O <- f])
  | redex_iteT_trueT :
    forall e f : termT,
    one_reduction (iteT trueT e f) e
  | redex_iteT_falseT :
    forall e f : termT,
    one_reduction (iteT falseT e f) f
  | redex_recT_oT :
    forall e f : termT,
    one_reduction (recT e f oT) e
  | redex_recT_sT :
    forall e f g : termT,
    one_reduction (recT e f (sT g)) (appT (appT f (recT e f g)) g)
  | redind_absT :
    forall e f : termT,
    one_reduction e f ->
    one_reduction (absT e) (absT f)
  | redind_appT_l :
    forall e f g : termT,
    one_reduction e f ->
    one_reduction (appT e g) (appT f g)
  | redind_appT_r :
    forall e f g : termT,
    one_reduction f g ->
    one_reduction (appT e f) (appT e g)
  | redind_iteT_l :
    forall e f g h : termT,
    one_reduction e f ->
    one_reduction (iteT e g h) (iteT f g h)
  | redind_iteT_c :
    forall e f g h : termT,
    one_reduction f g ->
    one_reduction (iteT e f h) (iteT e g h)
  | redind_iteT_r :
    forall e f g h : termT,
    one_reduction g h ->
    one_reduction (iteT e f g) (iteT e f h)
  | redind_sT :
    forall e f : termT,
    one_reduction e f ->
    one_reduction (sT e) (sT f)
  | redind_recT_l :
    forall e f g h : termT,
    one_reduction e f ->
    one_reduction (recT e g h) (recT f g h)
  | redind_recT_c :
    forall e f g h : termT,
    one_reduction f g ->
    one_reduction (recT e f h) (recT e g h)
  | redind_recT_r :
    forall e f g h : termT,
    one_reduction g h ->
    one_reduction (recT e f g) (recT e f h).

Notation "e ->1 f" := (one_reduction e f) (at level 80) : system_t_term_scope.

Inductive reduction : nat -> termT -> termT -> Prop :=
  | red_refl_zero : forall e : termT, reduction O e e
  | red_next :
    forall n : nat, forall e f g : termT,
    (e ->1 f) -> reduction n f g -> 
    reduction (S n) e g.

Notation "e ->( n ) f" := (reduction n e f) (at level 80) : system_t_term_scope.

Definition reduction_star (e f : termT) : Prop :=
    exists n : nat, e ->(n) f.

Notation "e ->* f" := (reduction_star e f) (at level 80) : system_t_term_scope.

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

Definition reductible (e : termT) : Prop :=
    exists f : termT, e ->1 f.

Fixpoint reductibleb (e : termT) : bool :=
  match e with
  | appT (absT _) _
  | iteT trueT _ _
  | iteT falseT _ _
  | recT _ _ oT
  | recT _ _ (sT _) => true
  | absT e
  | sT e => reductibleb e
  | appT e f => reductibleb e || reductibleb f
  | iteT e f g
  | recT e f g => reductibleb e || reductibleb f || reductibleb g
  | _ => false
  end.

Lemma reductibleb_spec :
    forall e : termT, Bool.reflect (reductible e) (reductibleb e).
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
  - inversion IHe1.
  --- simpl.
      rewrite <- H.
      simpl.
      destruct e1;
      left;
      destruct H0 as [g Hred];
      eexists;
      eauto using one_reduction.
Admitted. 

Fixpoint left_reduce (e : termT) : option termT :=
  match e with
  | appT (absT e) f => Some (e[O <- f])
  | iteT trueT e f => Some e
  | iteT falseT e f => Some f 
  | recT e f oT => Some e
  | recT e f (sT g) => Some (appT f (recT e f g))
  | absT e => option_map absT (left_reduce e)
  | sT e => option_map sT (left_reduce e)
  | appT e f =>
    match left_reduce e, left_reduce f with
    | Some e, _ => Some (appT e f)
    | _, Some f => Some (appT e f)
    | _, _ => None
    end
  | iteT e f g =>
    match left_reduce e, left_reduce f, left_reduce g with
    | Some e, _, _ => Some (iteT e f g)
    | _, Some f, _ => Some (iteT e f g)
    | _, _, Some g => Some (iteT e f g)
    | _, _, _ => None
    end
  | recT e f g =>
    match left_reduce e, left_reduce f, left_reduce g with
    | Some e, _, _ => Some (recT e f g)
    | _, Some f, _ => Some (recT e f g)
    | _, _, Some g => Some (recT e f g)
    | _, _, _ => None
    end
  | _ => None
  end.

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

Lemma left_reduce_reductible {e : termT} :
    reductible e -> exists f : termT, left_reduce e = Some f.
Admitted.

Definition reduction_one (e f : termT) : Prop := f ->1 e.

Notation "e 1<- f" := (reduction_one e f) (at level 80) : system_t_term_scope.

Definition strongly_normalizing (e : termT) : Prop := Acc reduction_one e.

Definition reduce (e : termT) :
    strongly_normalizing e -> termT.
Proof.
  intro HSN.
  induction HSN as [e].
  destruct (left_reduce e) eqn:Heq.
  - apply (X t).
    apply left_reduce_spec.
    exact Heq.
  - exact e. 
Defined.

Print reduce.

Lemma normal_form_strongly_normalizing {e : termT} :
    ~ reductible e -> strongly_normalizing e.
Proof.
  intro nred.
  constructor.
  intros y Hred.
  unfold "1<-" in Hred.
  destruct (nred ).
  eexists.
  eauto.
Defined.

Lemma normal_form_bvarT {n : nat} :
    ~ reductible (bvarT n).
Proof.
  intro nred.
  destruct nred.
  inversion H.
Defined.
