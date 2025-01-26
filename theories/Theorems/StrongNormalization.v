Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import Definitions.Ident.
Require Import Definitions.Term.
Require Import Definitions.Type.
Require Import Definitions.Typing.
Require Import Definitions.Reduction.
Require Import Theorems.Substitution.
Require Import Theorems.Reduction.
Require Import Theorems.NormalForm.
Require Import Morphisms.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.
Open Scope system_t_type_scope.

Lemma normal_form_strongly_normalizing {e : termT} :
    normal_form e -> strongly_normalizing e.
Proof.
  intro Hnf.
  constructor.
  intros f Hred.
  destruct Hnf.
  exists f.
  assumption.
Qed.

Lemma strongly_normalizing_f {e : termT} {r : termT -> termT} :
    (forall e f : termT, (r e ->1 r f) -> (e ->1 f)) ->
    (forall e f : termT, (r e ->1 f) -> exists g : termT, f = r g) ->
    strongly_normalizing e ->
    strongly_normalizing (r e).
Proof.
  move=> Himpl Hsur Hsn.
  induction Hsn as [f Hacc Hred1].
  constructor.
  move=> g Hred2.
  destruct (Hsur _ _ Hred2) as [h Heq].
  rewrite Heq.
  apply Hred1.
  apply Himpl.
  rewrite Heq in Hred2.
  assumption. 
Qed.

Lemma strongly_normalizing_f_inv {e : termT} {r : termT -> termT} :
    (forall e f : termT, (e ->1 f) -> (r e ->1 r f)) ->
    strongly_normalizing (r e) ->
    strongly_normalizing e.
Proof.
  generalize (eq_refl (r e)).
  pattern (r e) at -1.
  generalize (r e) at -2.
  simpl.
  move=> f Heq Himpl Hsn.
  rewrite <- Heq in Hsn.
  move: e Heq.
  induction Hsn as [f Hacc Hred1].
  move=> e Heq.
  constructor.
  move=> g Hred2.
  eapply Hred1.
  - unfold "1<-".
    rewrite Heq.
    apply Himpl.
    exact Hred2.
  - reflexivity.
Qed.

Lemma strongly_normalizing_bsubst_inv {e f : termT} {n : nat} :
    strongly_normalizing (e[n <- f]) ->
    strongly_normalizing e.
Proof.
  apply (strongly_normalizing_f_inv (r := fun e => e [n <- f])).
  eauto using one_reduction_bsubst_l.
Qed.

Lemma strongly_normalizing_one_reduction {e f : termT} :
    (e ->1 f) -> strongly_normalizing e ->
    strongly_normalizing f.
Proof.
  move=> Hred Hsn.
  destruct Hsn.
  apply H.
  assumption.
Qed.

Lemma strongly_normalizing_reduction {n : nat} {e f : termT} :
    (e ->(n) f) -> strongly_normalizing e ->
    strongly_normalizing f.
Proof.
  move=> Hred.
  induction Hred;
  auto.
  move=> Hsn.
  apply IHHred.
  apply (strongly_normalizing_one_reduction (e := e));
  assumption.
Qed.

Lemma strongly_normalizing_reduction_star {e f : termT} :
    (e ->* f) -> strongly_normalizing e ->
    strongly_normalizing f.
Proof.
  move=> [n Hred].
  exact (strongly_normalizing_reduction Hred).
Qed.

Fixpoint reducibility_candidate (t : typeT) : termT -> Prop :=
  match t with
  | funT t u =>
    fun e =>
      forall f : termT,
      reducibility_candidate t f ->
      reducibility_candidate u (appT e f)
  | prodT t u =>
    fun e =>
      reducibility_candidate t (plT e) /\
      reducibility_candidate u (prT e)
  | _ =>
    strongly_normalizing
  end.

Lemma reducibility_candidate_cr2 {t : typeT} {e f : termT} :
    (e ->1 f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  move: e f.
  induction t; simpl; move=> e f Hred Hredue;
    try (
      destruct Hredue as [Hsn];
      apply Hsn;
      assumption;
      fail
    ).
  - move=> g Hredug.
    apply (IHt2 (appT e g));
    auto using one_reduction.
  - destruct Hredue as [Hreduple Hredupre];
    eauto 6 using one_reduction.
Qed.

Lemma reducibility_candidate_reduction {t : typeT} {e f : termT} {n : nat} :
    (e ->(n) f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  move=> Hred.
  induction Hred;
  eauto using reducibility_candidate_cr2.
Qed.

Lemma reducibility_candidate_reduction_star {t : typeT} {e f : termT} :
    (e ->* f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  intro Hred.
  destruct Hred.
  eauto using reducibility_candidate_reduction.
Qed.    

Inductive neutral : termT -> Prop :=
  | neutral_fvarT : forall f : FIdent.t, neutral (fvarT f)
  | neutral_bvarT : forall n : nat, neutral (bvarT n)
  | neutral_appT : forall e f : termT, neutral (appT e f)
  | neutral_plT : forall e : termT, neutral (plT e)
  | neutral_prT : forall e : termT, neutral (prT e)
  | neutral_iteT : forall e f g : termT, neutral (iteT e f g)
  | neutral_recT : forall e f g : termT, neutral (recT e f g).

Lemma reducibility_candidate_cr_aux {t : typeT} :
    (forall e : termT,
      reducibility_candidate t e ->
      strongly_normalizing e) /\
    (forall e : termT,
      neutral e ->
      (forall f : termT, (e ->1 f) -> reducibility_candidate t f) ->
      reducibility_candidate t e).
Proof.
  induction t;
  try (
    constructor;
    auto;
    move=> e _ HAcc;
    constructor;
    assumption  
  );
  destruct IHt1 as [IHt11 IHt13];
  destruct IHt2 as [IHt21 IHt23].
  - constructor.
  --- move=> e Hredu.
      have bar : reducibility_candidate t1 (bvarT O).
      (*
        The choice of [bvarT O] is completely arbitrary.
        We only need the fact that [reducibility_candidate t1] is
        non-empty. This is the case because it contains [bvarT O],
        by (CR3).
      *)
  ----- apply IHt13.
  ------- eauto using neutral.
  ------- move=> f Hred.
          inversion Hred.
  ----- eapply (strongly_normalizing_f_inv (r := fun e => appT e _)).
  ------- eauto using one_reduction.
  ------- eapply IHt21.
          simpl in Hredu.
          apply (Hredu (bvarT O)).
          assumption.
  --- simpl.
      move=> e Hneut Hforall f Hreduf.
      have HAcc := IHt11 f Hreduf.
      induction HAcc.
      apply IHt23.
  ----- eauto using neutral.
  ----- move=> f Hred.
        inversion Hred.
  ------- rewrite <- H2 in Hneut.
          inversion Hneut.
  ------- apply Hforall;
          auto.
  ------- apply H0;
          auto.
          apply (reducibility_candidate_cr2 (e := x));
          assumption.
  - constructor.
  --- simpl.
      move=> e [Hreduple Hredupre].
      apply (strongly_normalizing_f_inv (r := plT));
      eauto using one_reduction.
  --- simpl.
      move=> e Hneut Hforall.
      constructor.
  ----- apply IHt13.
  ------- eauto using neutral.
  ------- move=> f Hred.
          inversion Hred.
  --------- rewrite <- H0 in Hneut.
            inversion Hneut.
  --------- destruct (Hforall f0 H0).
            assumption.
  ----- apply IHt23.
  ------- eauto using neutral.
  ------- move=> f Hred.
          inversion Hred.
  --------- rewrite <- H0 in Hneut.
            inversion Hneut.
  --------- destruct (Hforall f0 H0).
            assumption.
Qed.

Lemma reducibility_candidate_cr1 {t : typeT} {e : termT} :
    reducibility_candidate t e -> strongly_normalizing e.
Proof.
  move: e.
  exact reducibility_candidate_cr_aux.1.
Qed.

Lemma reducibility_candidate_cr3 {t : typeT} {e : termT} :
    neutral e ->
    (forall f : termT, (e ->1 f) -> reducibility_candidate t f) ->
    reducibility_candidate t e.
Proof.
  move: e.
  exact reducibility_candidate_cr_aux.2.
Qed.

Lemma reducibility_candidate_normal_form {t : typeT} {e : termT} :
    neutral e -> normal_form e -> reducibility_candidate t e.
Proof.
  move=> Hneut Hnf.
  apply reducibility_candidate_cr3.
  - assumption.
  - move=> f Hred.
    destruct Hnf.
    eexists.
    eauto. 
Qed.

Lemma reducibility_candidate_fvarT {t : typeT} {x : FIdent.t} :
    reducibility_candidate t (fvarT x).
Proof.
  apply reducibility_candidate_normal_form.
  - eauto using neutral.
  - exact normal_form_fvarT.
Qed.

Lemma reducibility_candidate_bvarT {t : typeT} {n : nat} :
    reducibility_candidate t (bvarT n).
Proof.
  apply reducibility_candidate_normal_form.
  - eauto using neutral.
  - exact normal_form_bvarT.
Qed.

Lemma reducibility_candidate_absT {t u : typeT} {e : termT} :
    (forall f : termT,
      reducibility_candidate t f ->
      reducibility_candidate u (e[O <- f])) ->
    reducibility_candidate (t ->T u) (absT e).
Proof.
  move=> Hforall.
  have Hsn :=
    strongly_normalizing_bsubst_inv
      (reducibility_candidate_cr1
        (Hforall (bvarT O) reducibility_candidate_bvarT)).
  simpl.
  induction Hsn.
  move=> f Hreduf.
  clear H.
  have Hsn := reducibility_candidate_cr1 Hreduf.
  induction Hsn.
  apply reducibility_candidate_cr3.
  - eauto using neutral.
  - move=> f Hred.
    inversion Hred;
    auto.
  --- inversion H5.
      apply H0;
      auto.
      move=> h Hreduh.
      eauto using reducibility_candidate_cr2, one_reduction_bsubst_l.
  --- apply H1;
      auto.
      eauto using reducibility_candidate_cr2.
Qed.

Lemma reducibility_candidate_appT {t u : typeT} {e f : termT} :
    reducibility_candidate (t ->T u) e ->
    reducibility_candidate t f ->
    reducibility_candidate u (appT e f).
Proof.
  eauto.
Qed.

Lemma reducibility_candidate_pairT {t u : typeT} {e f : termT} :
    reducibility_candidate t e ->
    reducibility_candidate u f ->
    reducibility_candidate (t *T u) (pairT e f).
Proof.
  move=> Hredue.
  move: f.
  have Hsn := reducibility_candidate_cr1 Hredue.
  induction Hsn as [e _ Hinde].
  move=> f Hreduf.
  have Hsn := reducibility_candidate_cr1 Hreduf.
  induction Hsn as [f _ Hindf];
  constructor;
  apply reducibility_candidate_cr3;
  eauto using neutral.
  - move=> g Hredg.
    inversion Hredg.
  --- rewrite <- H2.
      assumption.
  --- inversion H0.
  ----- simpl in Hinde.
        destruct (
          Hinde f1 H5
            (reducibility_candidate_cr2 H5 Hredue)
            f Hreduf
        ).
        assumption.
  ----- simpl in Hindf.
        destruct (
          Hindf g0 H5
            (reducibility_candidate_cr2 H5 Hreduf)
        ).
        assumption.
  - move=> g Hredg.
    inversion Hredg.
  --- rewrite <- H2.
      assumption.
  --- inversion H0.
  ----- simpl in Hinde.
        destruct (
          Hinde f1 H5
            (reducibility_candidate_cr2 H5 Hredue)
            f Hreduf
        ).
        assumption.
  ----- simpl in Hindf.
        destruct (
          Hindf g0 H5
            (reducibility_candidate_cr2 H5 Hreduf)
        ).
        assumption.
Qed.

Lemma reducibility_candidate_plT {t u : typeT} {e : termT} :
    reducibility_candidate (t *T u) e ->
    reducibility_candidate t (plT e).
Proof.
  simpl.
  move=> [Hredu _].
  assumption.
Qed.

Lemma reducibility_candidate_prT {t u : typeT} {e : termT} :
    reducibility_candidate (t *T u) e ->
    reducibility_candidate u (prT e).
Proof.
  simpl.
  move=> [_ Hredu].
  assumption.
Qed.

Lemma reducibility_candidate_falseT :
    reducibility_candidate boolT falseT.
Proof.
  apply normal_form_strongly_normalizing.
  exact (normal_form_bool_as_boolT (b := false)).
Qed.

Lemma reducibility_candidate_trueT :
    reducibility_candidate boolT trueT.
Proof.
  apply normal_form_strongly_normalizing.
  exact (normal_form_bool_as_boolT (b := true)).
Qed.

Lemma reducibility_candidate_iteT {t : typeT} {e f g : termT} :
    reducibility_candidate boolT e ->
    reducibility_candidate t f ->
    reducibility_candidate t g ->
    reducibility_candidate t (iteT e f g).
Proof.
  move=> Hredue.
  move: f g.
  induction Hredue as [e _ Hinde].
  move=> f g Hreduf.
  move: g.
  have Hsn := reducibility_candidate_cr1 Hreduf.
  induction Hsn as [f _ Hindf].
  move=> g Hredug.
  have Hsn := reducibility_candidate_cr1 Hredug.
  induction Hsn as [g _ Hindg].
  apply reducibility_candidate_cr3.
  - auto using neutral.
  - move=> h Hredu.
    inversion Hredu;
    eauto using reducibility_candidate_cr2;
    rewrite <- H3;
    assumption.
Qed.

Lemma reducibility_candidate_oT :
    reducibility_candidate natT oT.
Proof.
  apply normal_form_strongly_normalizing.
  exact (normal_form_nat_as_natT (n := O)).
Qed.

Lemma reducibility_candidate_sT {e : termT} :
    reducibility_candidate natT e ->
    reducibility_candidate natT (sT e).
Proof.
  apply strongly_normalizing_f;
  move=> f g Hred;
  inversion Hred;
  eauto.
Qed.

Definition sT_rel (e f : termT) : Prop := f = sT e.

Definition reduction_one_or_sT (e f : termT) :=
    e 1<- f \/ sT_rel e f.

Lemma wf_sT_rel : well_founded sT_rel.
Proof.
  move=> e.
  induction e;
  constructor; move=> h Heq;
  try discriminate Heq.
  inversion Heq.
  rewrite <- H0.
  assumption.
Qed.  

Lemma strongly_normalizing_acc_one_or_sT {e : termT} :
    strongly_normalizing e ->
    Acc reduction_one_or_sT e.
Proof.
  move=> Hsn.
  induction Hsn as [e Hacc1 Hind1].
  have Hacc2 := wf_sT_rel e.
  induction Hacc2 as [e Hacc2 Hind2].
  constructor.
  move=> f [Hred | HsT].
  - auto.
  - inversion HsT.
    apply Hind2;
    auto.
  --- move=> g Hred.
      have foo : strongly_normalizing (sT f).
      constructor.
      rewrite <- H.
      assumption.
      have bar : strongly_normalizing f.
      apply (strongly_normalizing_f_inv (r := sT)).
      eauto using one_reduction.
      assumption.
      destruct bar as [bar].
      apply bar.
      assumption.
  --- move=> g Hred.
      have foo : Acc reduction_one_or_sT (sT g).
      apply Hind1.
      rewrite H.
      unfold "1<-".
      eauto using one_reduction.
      destruct foo as [foo].
      apply foo.
      right.
      reflexivity.
Qed.

Lemma reducibility_candidate_recT {t : typeT} {e f g : termT} :
    reducibility_candidate t e ->
    reducibility_candidate (t ->T natT ->T t) f ->
    reducibility_candidate natT g ->
    reducibility_candidate t (recT e f g).
Proof.
  move=> Hredue.
  move: f g.
  have Hsn := reducibility_candidate_cr1 Hredue.
  induction Hsn as [e _ Hinde].
  move=> f g Hreduf.
  move: g.
  have Hsn := reducibility_candidate_cr1 Hreduf.
  induction Hsn as [f _ Hindf].
  move=> g Hredug.
  have Hsn := strongly_normalizing_acc_one_or_sT Hredug.
  induction Hsn as [g _ Hindg].
  apply reducibility_candidate_cr3;
  try (
    auto using neutral;
    move=> h Hred;
    inversion Hred;
    eauto using reducibility_candidate_cr2;
    try (apply Hindg;
      try (
        left;
        assumption
      )
    );
    eauto using reducibility_candidate_cr2
  ).
  - rewrite <- H3.
    assumption. 
  - simpl in Hreduf.
    apply Hreduf.
  --- apply Hindg.
  ----- right.
        symmetry.
        assumption.
  ----- apply (strongly_normalizing_f_inv (r := sT)).
  ------- eauto using one_reduction.
  ------- rewrite H2.
          assumption.
  --- apply (strongly_normalizing_f_inv (r := sT)).
  ----- eauto using one_reduction.
  ----- rewrite H2.
        assumption.
Qed.

Hint Resolve
  reducibility_candidate_fvarT
  reducibility_candidate_bvarT
  reducibility_candidate_absT
  reducibility_candidate_appT
  reducibility_candidate_pairT
  reducibility_candidate_plT
  reducibility_candidate_prT
  reducibility_candidate_falseT
  reducibility_candidate_trueT
  reducibility_candidate_iteT
  reducibility_candidate_oT
  reducibility_candidate_sT
  reducibility_candidate_recT : reducibility_candidate_lemmas.

Lemma reducibility_candidate_par_bsubst_derivation
  {t : typeT} {e : termT} {G : Context.t} {s : list termT} :
    (forall (n : nat) (t : typeT) (e : termT),
      Context.bMapsTo n t G ->
      List.nth_error s n = Some e ->
      reducibility_candidate t e) ->
    G |- e :T t -> reducibility_candidate t (par_bsubst O s e).
Proof.
  move=> Hmap Hderiv.
  move: s Hmap.
  induction Hderiv;
  move=> s Hmap;
  eauto with reducibility_candidate_lemmas;
  simpl;
  try constructor;
  eauto with reducibility_candidate_lemmas.
  - rewrite Nat.sub_0_r.
    destruct (List.nth_error s n) as [u | ] eqn:Heq.
  --- apply (Hmap n);
      auto.
  --- exact reducibility_candidate_bvarT. 
  - move=> f Hredu.
    apply (reducibility_candidate_appT (t := t)).
  --- apply reducibility_candidate_absT.
      move=> g Hredug.
      rewrite par_bsubst_bsubst_eq.
      apply IHHderiv.
      move=> n v h Hmap2 Heq.
      destruct n;
      simpl in Heq;
      unfold Context.bMapsTo in Hmap2;
      simpl in Hmap2.
  ----- inversion Heq.
        inversion Hmap2.
        rewrite <- H0.
        rewrite <- H1.
        assumption.
  ----- apply (Hmap n);
        auto. 
  --- assumption. 
  - apply reducibility_candidate_sT.
    auto. 
Qed.

Lemma reducibility_candidate_derivation {G : Context.t} {t : typeT} {e : termT} :
    G |- e :T t -> reducibility_candidate t e.
Proof.
  rewrite <- (par_bsubst_empty (n := O)) at -1.
  apply (reducibility_candidate_par_bsubst_derivation (s := nil)).
  move=> [ | n] u f _ Heq;
  simpl in Heq;
  discriminate Heq.
Qed.

Theorem derivation_strongly_normalizing
  {e : termT} {t : typeT} {G : Context.t} :
    G |- e :T t -> strongly_normalizing e.
Proof.
  move=> Hderiv.
  eapply reducibility_candidate_cr1.
  eapply reducibility_candidate_derivation.
  exact Hderiv.
Qed.
