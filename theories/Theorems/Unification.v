Require Import Definitions.Type.
Require Import Theorems.Type.

Require Import List.
Require Import Morphisms.

Require Import ssreflect ssrfun ssrbool.

#[export] Instance Proper_unifies : Morphisms.Proper (ext_equal ==> eq ==> eq ==> iff)
    unifies.
Proof.
  move=> r s Heq1 t u Heq2 v w Heq3;
  rewrite Heq2.
  rewrite Heq3.
  unfold unifies.
  repeat rewrite (Heq1 _).
  reflexivity.
Qed.

#[export] Instance Proper_solves : Morphisms.Proper (ext_equal ==> eq ==> iff)
    solves.
Proof.
  move=> r s Heq1 p q Heq2.
  rewrite Heq2.
  clear p Heq2.
  induction q as [ | [t u] q].
  - constructor;
    move=> _;
    left.
  - constructor;
    move=> Hsol;
    inversion Hsol as [ | c l Huni Hforall Heq2];
    clear c l Heq2 H;
    right;
    try rewrite <- Heq1;
    try rewrite <- IHq;
    try rewrite <- Heq1 in Huni;
    try rewrite <- IHq in Hforall;
    assumption.
Qed.

Lemma wf_unification_problem_order :
  well_founded unification_problem_order.
Proof.
  move=> p.
  generalize (PeanoNat.Nat.le_refl (problem_size p)).
  generalize (problem_size p) at -1.
  generalize (PeanoNat.Nat.le_refl (TSet.cardinal (problem_variable_set p))).
  generalize (TSet.cardinal (problem_variable_set p)) at -1.
  move=> n.
  move: p.
  induction n;
  move=> p Hle1 m;
  move: p Hle1;
  induction m;
  move=> p Hle1 Hle2;
  constructor;
  move=> q [Hlt | Hle Hlt];
  try Lia.lia.
  - apply IHm;
    Lia.lia.
  - eapply IHn.
  --- Lia.lia.
  --- apply PeanoNat.Nat.le_refl.
  - eapply IHn.
  --- Lia.lia.
  --- apply PeanoNat.Nat.le_refl.
  - apply IHm;
    Lia.lia.
Qed.

Lemma par_tsubst_occur {x : TIdent.t} {s : TMap.t typeT} {t : typeT} :
    occurs x t = true ->
    unifies s (tvarT x) t ->
    t = tvarT x.
Proof.
  move=> Hocc Hunif.
  destruct t;
  inversion Hocc.
  - move/ TIdentFacts.eqb_spec in H0.
    rewrite H0.
    reflexivity.
  - simpl in Hocc.
    have Habs :
      size (par_tsubst s (t1 ->T t2)) >
      size (par_tsubst s (tvarT x)).
  --- simpl (size (par_tsubst s (t1 ->T t2))).
      destruct (occurs x t1) eqn:Heq.
  ----- have Hcomp1 := par_tsubst_size Heq.
        have Hcomp2 := Hcomp1 s.
        Lia.lia.
  ----- simpl in H0.
        have Hcomp1 := par_tsubst_size H0.
        have Hcomp2 := Hcomp1 s.
        Lia.lia.
  --- rewrite Hunif in Habs.
      Lia.lia.
  - simpl in Hocc.
    have Habs :
      size (par_tsubst s (t1 *T t2)) >
      size (par_tsubst s (tvarT x)).
  --- simpl (size (par_tsubst s (t1 *T t2))).
      destruct (occurs x t1) eqn:Heq.
  ----- have Hcomp1 := par_tsubst_size Heq.
        have Hcomp2 := Hcomp1 s.
        Lia.lia.
  ----- simpl in H0.
        have Hcomp1 := par_tsubst_size H0.
        have Hcomp2 := Hcomp1 s.
        Lia.lia.
  --- rewrite Hunif in Habs.
      Lia.lia.
Qed.

Lemma par_tsubst_nooccur {x : TIdent.t} {s : TMap.t typeT} {t : typeT} :
    unifies s (tvarT x) t ->
    t <> tvarT x ->
    occurs x t = false.
Proof.
  move=> Hunif Hneq.
  destruct (occurs x t) eqn:Heq.
  - destruct (Hneq (par_tsubst_occur Heq Hunif)).
  - reflexivity.
Qed.

Lemma par_tsubst_tsubst_factor
  {s : TMap.t typeT} {x : TIdent.t} {t : typeT} :
    unifies s (tvarT x) t ->
    s >>= (| x |-> t |) >>> s.
Proof.
  move=> Heq u.
  induction u;
  simpl;
  f_equal;
  eauto.
  unfold tsubst_add_r.
  rewrite TMapFacts.add_o.
  destruct (TMapFacts.eq_dec x s0) as [Heq2 | Hneq2].
  - fold (par_tsubst s (tvarT s0)).
    rewrite <- Heq2.
    assumption.
  - reflexivity. 
Qed.

Lemma par_tsubst_tsubst_solves
  {s : TMap.t typeT} {x : TIdent.t} {t : typeT} {p : unification_problem} :
    unifies s (tvarT x) t ->
    solves s p ->
    solves s (unification_problem_tsubst x t p).
Proof.
  move=> Hunif.
  induction p as [ | [u v] p].
  - left.
  - move=> Hsol.
    inversion Hsol.
    right.
  --- simpl.
      simpl in H1.
      unfold unifies.
      repeat rewrite par_tsubst_tsubst.
      repeat rewrite <- par_tsubst_tsubst_factor;
      assumption.
  --- apply IHp.
      assumption.
Qed.

Lemma unify_aux_funT {t u v w : typeT} {p q : unification_problem} :
    p = (t ->T u, v ->T w) :: q ->
    unification_problem_order ((t, v) :: (u, w) :: q) p.
Proof.
  move=> Heq.
  rewrite Heq.
  right;
  simpl.
  - repeat rewrite TSetFacts.union_assoc.
    rewrite <- (TSetFacts.union_assoc (variable_set v)).
    rewrite (TSetFacts.union_sym (variable_set v)).
    rewrite TSetFacts.union_assoc.
    reflexivity.
  - Lia.lia.
Qed.

Lemma unify_aux_prodT {t u v w : typeT} {p q : unification_problem} :
    p = (t *T u, v *T w) :: q ->
    unification_problem_order ((t, v) :: (u, w) :: q) p.
Proof.
  move=> Heq.
  rewrite Heq.
  right;
  simpl.
  - repeat rewrite TSetFacts.union_assoc.
    rewrite <- (TSetFacts.union_assoc (variable_set v)).
    rewrite (TSetFacts.union_sym (variable_set v)).
    rewrite TSetFacts.union_assoc.
    reflexivity.
  - Lia.lia.
Qed.

Lemma unify_aux_eq {t u : typeT} {p q : unification_problem} :
    p = (t, u) :: q ->
    unification_problem_order q p.
Proof.
  move=> Heq.
  rewrite Heq.
  right.
  - simpl.
    apply TSetFacts.subset_cardinal.
    apply TSetFacts.union_subset_2.
  - induction t;
    simpl;
    Lia.lia.
Qed.

Lemma unify_aux_subset
  {x : TIdent.t} {t : typeT} {p :unification_problem} :
    TSet.Subset
      (problem_variable_set (unification_problem_tsubst x t p))
      (TSet.union
        (TSet.union
          (variable_set (tvarT x)) (variable_set t))
        (problem_variable_set p)).
Proof.
  induction p;
  simpl.
  - apply TSetFacts.subset_empty.
  - destruct a as [u v].
    simpl.
    apply TSetFacts.union_subset_3.
  --- have Hsub1 := @tsubst_subset x t u.
      have Hsub2 := @tsubst_subset x t v.
      TSetFacts.fsetdec.
  --- transitivity
        (TSet.union (TSet.union (variable_set (tvarT x)) (variable_set t))
        (problem_variable_set p)).
  ----- assumption.
  ----- simpl.
        TSetFacts.fsetdec.
Qed.

Lemma unify_aux_nooccur
  {x : TIdent.t} {t : typeT} {p :unification_problem} :
    ~TSet.In x (variable_set t) ->
    ~TSet.In x 
      (problem_variable_set (unification_problem_tsubst x t p)).
Proof.
  move=> Hnooccur.
  induction p as [ | [u v] p];
  simpl.
  - TSetFacts.fsetdec.
  - have Hnooccur1 := @tsubst_preserves_nooccur x t u.
    have Hnooccur2 := @tsubst_preserves_nooccur x t v.
    TSetFacts.fsetdec.
Qed.

Lemma unify_aux_tsubst_l
  {x : TIdent.t} {t : typeT} {p q : unification_problem} :
    occurs x t = false ->
    p = (tvarT x, t) :: q ->
    unification_problem_order (unification_problem_tsubst x t q) p.
Proof.
  move=> Hnooccur Heq.
  rewrite Heq.
  move/ occurs_spec in Hnooccur.
  left.
  apply (TSetFacts.subset_cardinal_lt (x := x));
  simpl.
  - exact unify_aux_subset.
  - TSetFacts.fsetdec.
  - apply unify_aux_nooccur.
    assumption.
Qed.

Lemma unify_aux_tsubst_r
  {x : TIdent.t} {t : typeT} {p q : unification_problem} :
    occurs x t = false ->
    p = (t, tvarT x) :: q ->
    unification_problem_order (unification_problem_tsubst x t q) p.
Proof.
  move=> Hnooccur Heq.
  rewrite Heq.
  move/ occurs_spec in Hnooccur.
  left.
  apply (TSetFacts.subset_cardinal_lt (x := x));
  simpl.
  - rewrite (TSetFacts.union_sym (variable_set t)).
    exact unify_aux_subset.
  - TSetFacts.fsetdec.
  - apply unify_aux_nooccur.
    assumption.
Qed.

Inductive list_eq {A : Type} (l : list A) :=
  | list_eq_nil : l = nil -> list_eq l
  | list_eq_cons : forall (a : A) (m : list A), l = a :: m -> list_eq l.

Inductive bool_eq (b : bool) :=
  | bool_eq_true : b = true -> bool_eq b
  | bool_eq_false : b = false -> bool_eq b.

Definition bool_as_bool_eq (b : bool) :
    bool_eq b :=
  match b with
  | true => bool_eq_true true (eq_refl true)
  | _ => bool_eq_false false (eq_refl false)
  end.

Definition list_as_list_eq {A : Type} (l : list A) :
    list_eq l :=
  match l with
  | nil => list_eq_nil nil (eq_refl nil)
  | a :: l => list_eq_cons (a :: l) a l (eq_refl (a :: l))
  end.

Fixpoint unify_aux
  (p : unification_problem)
  (ACC : Acc unification_problem_order p) :
    result (TMap.t typeT) unification_error :=
  match (list_as_list_eq p) with
  | list_eq_nil _ _ => ok (@TMap.empty typeT)
  | list_eq_cons _ (tvarT x, tvarT y as t) q Heq =>
    match bool_as_bool_eq (occurs x t) with
    | bool_eq_true _ _ => unify_aux q (Acc_inv ACC (unify_aux_eq Heq))
    | bool_eq_false _ Heq2 =>
      result_map
        (tsubst_add_r x t)
        (unify_aux
          (unification_problem_tsubst x t q)
          (Acc_inv ACC (unify_aux_tsubst_l Heq2 Heq)))
    end
  | list_eq_cons _ (t ->T u, v ->T w) q Heq =>
    unify_aux ((t, v) :: (u, w) :: q) (Acc_inv ACC (unify_aux_funT Heq))
  | list_eq_cons _ (t *T u, v *T w) q Heq =>
    unify_aux ((t, v) :: (u, w) :: q) (Acc_inv ACC (unify_aux_prodT Heq))
  | list_eq_cons _ (tvarT x, t) q Heq =>
    match bool_as_bool_eq (occurs x t) with
    | bool_eq_true _ _  => err (tvarT_occurs x t)
    | bool_eq_false _ Heq2 =>
      result_map
        (tsubst_add_r x t)
        (unify_aux
          (unification_problem_tsubst x t q)
          (Acc_inv ACC (unify_aux_tsubst_l Heq2 Heq)))
    end
  | list_eq_cons _ (t, tvarT x) q Heq =>
    match bool_as_bool_eq (occurs x t) with
    | bool_eq_true _ _  => err (tvarT_occurs x t)
    | bool_eq_false _ Heq2 =>
      result_map
        (tsubst_add_r x t)
        (unify_aux
          (unification_problem_tsubst x t q)
          (Acc_inv ACC (unify_aux_tsubst_r Heq2 Heq)))
    end
  | list_eq_cons _ (boolT, boolT) q Heq
  | list_eq_cons _ (natT, natT) q Heq =>
     unify_aux q (Acc_inv ACC (unify_aux_eq Heq))
  | list_eq_cons _ (t, u) q Heq =>
    err (different_constructors t u)
  end.

Definition unify (p : unification_problem) :
    result (TMap.t typeT) unification_error :=
  unify_aux p (wf_unification_problem_order p).

Lemma result_map_eq_ok_inv
  {A B C : Type} {f : A -> B} {r : result A C} {b : B} :
    result_map f r = ok b ->
    exists a : A, r = ok a.
Proof.
  move=> Heq.
  destruct r;
  try discriminate Heq.
  eauto.
Qed.

Lemma solves_tsubst_add_r
  {s : TMap.t typeT} {p : unification_problem}
  {x : TIdent.t} {t : typeT} :
    solves s (unification_problem_tsubst x t p) ->
    solves (tsubst_add_r x t s) p.
Proof.
  induction p as [ | [u v] p];
  move=> Hsol;
  inversion Hsol as [ | [w r] q Huni Hforall].
  - left.
  - right.
  --- simpl in Huni.
      simpl.
      unfold unifies.
      repeat rewrite <- par_tsubst_tsubst.
      assumption.
  --- apply IHp.
      assumption.
Qed.

Lemma unify_aux_sound
  {p : unification_problem} {ACC : Acc unification_problem_order p}
  {s : TMap.t typeT} :
    unify_aux p ACC = ok s -> solves s p.
Proof.
  move: s.
  induction p using (well_founded_induction wf_unification_problem_order);
  move=> s Heq.
  destruct ACC.
  destruct p as [
    | [t u] p].
  - left.
  - destruct t;
    destruct u;
    simpl in Heq;
    try discriminate Heq;
    try (
      destruct (result_map_eq_ok_inv Heq) as [r Heq2];
      rewrite Heq2 in Heq;
      simpl in Heq;
      inversion Heq as [Heq1];
      clear Heq
    );
    try (
      constructor; [
        simpl;
        unfold unifies;
        repeat rewrite <- par_tsubst_tsubst;
        f_equal;
        simpl;
        rewrite TIdentFacts.eqb_refl;
        reflexivity |
        apply solves_tsubst_add_r;
        eapply H; [
          try (
            apply unify_aux_tsubst_l;
            eauto;
            fail
          );
          try (
            apply unify_aux_tsubst_r;
            eauto;
            fail
          ) |
          exact Heq2
        ]
      ];
      fail
    ).
  --- constructor.
  ----- reflexivity.
  ----- eapply H.
  ------- eapply unify_aux_eq.
          reflexivity.
  ------- exact Heq.
  --- constructor.
  ----- reflexivity.
  ----- eapply H.
  ------- eapply unify_aux_eq.
          reflexivity.
  ------- exact Heq.
  --- destruct (bool_as_bool_eq (TIdentFacts.eqb s0 s1));
      constructor.
  ----- simpl;
        unfold unifies;
        move/ TIdentFacts.eqb_spec in e.
        rewrite e.
        reflexivity.
  ----- eapply H.
        eapply unify_aux_eq.
  -------- reflexivity.
  -------- exact Heq.   
  ----- try (
            destruct (result_map_eq_ok_inv Heq) as [r Heq2];
            rewrite Heq2 in Heq;
            simpl in Heq;
            inversion Heq as [Heq1];
            clear Heq
          ).
          unfold unifies.
          repeat rewrite <- par_tsubst_tsubst.
          f_equal.
          simpl.
          rewrite TIdentFacts.eqb_refl.
          rewrite e.
          reflexivity.
  ----- try (
            destruct (result_map_eq_ok_inv Heq) as [r Heq2];
            rewrite Heq2 in Heq;
            simpl in Heq;
            inversion Heq as [Heq1];
            clear Heq
          ).
        apply solves_tsubst_add_r.
        eapply H; eauto.
        apply unify_aux_tsubst_l;
        eauto.
  --- destruct (bool_as_bool_eq (occurs s0 u1 || occurs s0 u2));
      try (
        inversion Heq;
        fail
      ).
      try (
        destruct (result_map_eq_ok_inv Heq) as [r Heq2];
        rewrite Heq2 in Heq;
        simpl in Heq;
        inversion Heq as [Heq1];
        clear Heq
      );
      constructor; simpl.
  ----- unfold unifies.
        repeat rewrite <- par_tsubst_tsubst.
        f_equal.
        rewrite (tsubst_nooccur (u := u1 ->T u2)).
  ------- apply/ occurs_spec.
          simpl.
          rewrite e.
          auto.
  ------- simpl.
          rewrite TIdentFacts.eqb_refl.
          reflexivity.
  ----- apply solves_tsubst_add_r.
        eapply H;
        eauto.
        apply unify_aux_tsubst_l;
        eauto.
  --- destruct (bool_as_bool_eq (occurs s0 u1 || occurs s0 u2));
      try (
        inversion Heq;
        fail
      ).
      try (
        destruct (result_map_eq_ok_inv Heq) as [r Heq2];
        rewrite Heq2 in Heq;
        simpl in Heq;
        inversion Heq as [Heq1];
        clear Heq
      );
      constructor; simpl.
  ----- unfold unifies.
        repeat rewrite <- par_tsubst_tsubst.
        f_equal.
        rewrite (tsubst_nooccur (u := u1 *T u2)).
  ------- apply/ occurs_spec.
          simpl.
          rewrite e.
          auto.
  ------- simpl.
          rewrite TIdentFacts.eqb_refl.
          reflexivity.
  ----- apply solves_tsubst_add_r.
        eapply H;
        eauto.
        apply unify_aux_tsubst_l;
        eauto.
  --- destruct (bool_as_bool_eq (occurs s0 t1 || occurs s0 t2));
      try (
        inversion Heq;
        fail
      ).
      try (
        destruct (result_map_eq_ok_inv Heq) as [r Heq2];
        rewrite Heq2 in Heq;
        simpl in Heq;
        inversion Heq as [Heq1];
        clear Heq
      );
      constructor; simpl.
  ----- unfold unifies.
        repeat rewrite <- par_tsubst_tsubst.
        f_equal.
        rewrite (tsubst_nooccur (u := t1 ->T t2)).
  ------- apply/ occurs_spec.
          simpl.
          rewrite e.
          auto.
  ------- simpl.
          rewrite TIdentFacts.eqb_refl.
          reflexivity.
  ----- apply solves_tsubst_add_r.
        eapply H;
        eauto.
        apply unify_aux_tsubst_r;
        eauto.
  --- have Hsol : solves s ((t1, u1) :: (t2, u2) :: p).
  ----- eapply H.
  ------- apply unify_aux_funT.
          reflexivity.
  ------- exact Heq. 
  ----- inversion Hsol.
        inversion H3.
        constructor.
  ------- unfold unifies.
          simpl.
          simpl in H2.
          simpl in H6.
          f_equal;
          assumption.
  ------- assumption. 
  --- destruct (bool_as_bool_eq (occurs s0 t1 || occurs s0 t2));
      try (
        inversion Heq;
        fail
      ).
      try (
        destruct (result_map_eq_ok_inv Heq) as [r Heq2];
        rewrite Heq2 in Heq;
        simpl in Heq;
        inversion Heq as [Heq1];
        clear Heq
      );
      constructor; simpl.
  ----- unfold unifies.
        repeat rewrite <- par_tsubst_tsubst.
        f_equal.
        rewrite (tsubst_nooccur (u := t1 *T t2)).
  ------- apply/ occurs_spec.
          simpl.
          rewrite e.
          auto.
  ------- simpl.
          rewrite TIdentFacts.eqb_refl.
          reflexivity.
  ----- apply solves_tsubst_add_r.
        eapply H;
        eauto.
        apply unify_aux_tsubst_r;
        eauto.
  --- have Hsol : solves s ((t1, u1) :: (t2, u2) :: p).
  ----- eapply H.
  ------- apply unify_aux_prodT.
          reflexivity.
  ------- exact Heq. 
  ----- inversion Hsol.
        inversion H3.
        constructor.
  ------- unfold unifies.
          simpl.
          simpl in H2.
          simpl in H6.
          f_equal;
          assumption.
  ------- assumption.
Qed.

Lemma tsubst_add_r_absorbs {x : TIdent.t} {t: typeT}
  {s : TMap.t typeT} :
    unifies s (tvarT x) t ->
    (|x |-> t|) >>> s >>= s.
Proof.
  move=> Hunif u.
  induction u;
  simpl;
  f_equal;
  auto.
  rewrite TMapFacts.add_o.
  destruct (TMapFacts.eq_dec x s0).
  - repeat rewrite <- e.
    fold (par_tsubst s (tvarT x)).
    symmetry.
    assumption.
  - reflexivity.  
Qed.

Lemma unify_aux_complete
  {p : unification_problem} {ACC : Acc unification_problem_order p}
  {s : TMap.t typeT} :
    solves s p -> exists r : TMap.t typeT, unify_aux p ACC = ok r /\
    s >>= r >>> s.
Proof.
  move: s.
  induction p using (well_founded_induction wf_unification_problem_order);
  move=> s Hsol.
  destruct ACC.
  destruct p as [
    | [t u] p];
    simpl.
  - exists (TMap.empty _).
    constructor.
  --- reflexivity. 
  --- rewrite tsubst_compose_empty_l.
      reflexivity.
  - destruct t;
    destruct u;
    inversion Hsol;
    try (
      eapply H; [
        eapply unify_aux_eq;
        reflexivity |
        exact H3
      ]
    );
    try inversion H2;
    simpl in H2.
  --- simpl.
      symmetry in H2.
      edestruct H as [r [Heq1 Heq2]].
  ----- eapply unify_aux_tsubst_r.
  ------- apply (par_tsubst_nooccur (s := s)).
  --------- exact H2.
  --------- discriminate.
  ------- reflexivity.
  ----- apply par_tsubst_tsubst_solves.
  ------- exact H2.
  ------- assumption.
  ----- rewrite Heq1.
        simpl.
        exists (tsubst_add_r s0 natT r).
        constructor.
  ------- reflexivity.
          Unshelve.
          apply a.
          apply unify_aux_tsubst_r;
          auto.
  ------- rewrite tsubst_compose_tsubst_add_r.
          rewrite <- Heq2.
          symmetry.
          apply tsubst_add_r_absorbs.
          assumption.
  --- simpl.
      symmetry in H2.
      edestruct H as [r [Heq1 Heq2]].
  ----- eapply unify_aux_tsubst_r.
  ------- apply (par_tsubst_nooccur (s := s)).
  --------- exact H2.
  --------- discriminate.
  ------- reflexivity.
  ----- apply par_tsubst_tsubst_solves.
  ------- exact H2.
  ------- assumption.
  ----- rewrite Heq1.
        simpl.
        exists (tsubst_add_r s0 boolT r).
        constructor.
  ------- reflexivity.
          Unshelve.
          apply a.
          apply unify_aux_tsubst_r;
          auto.
  ------- rewrite tsubst_compose_tsubst_add_r.
          rewrite <- Heq2.
          symmetry.
          apply tsubst_add_r_absorbs.
          assumption.
  --- simpl.
      edestruct H as [r [Heq1 Heq2]].
  ----- eapply unify_aux_tsubst_l.
  ------- apply (par_tsubst_nooccur (s := s)).
  --------- exact H2.
  --------- discriminate.
  ------- reflexivity.
  ----- apply par_tsubst_tsubst_solves.
  ------- exact H2.
  ------- assumption.
  ----- rewrite Heq1.
        simpl.
        exists (tsubst_add_r s0 natT r).
        constructor.
  ------- reflexivity.
          Unshelve.
          apply a.
          apply unify_aux_tsubst_l;
          auto.
  ------- rewrite tsubst_compose_tsubst_add_r.
          rewrite <- Heq2.
          symmetry.
          apply tsubst_add_r_absorbs.
          assumption.
  --- simpl.
      edestruct H as [r [Heq1 Heq2]].
  ----- eapply unify_aux_tsubst_l.
  ------- apply (par_tsubst_nooccur (s := s)).
  --------- exact H2.
  --------- discriminate.
  ------- reflexivity.
  ----- apply par_tsubst_tsubst_solves.
  ------- exact H2.
  ------- assumption.
  ----- rewrite Heq1.
        simpl.
        exists (tsubst_add_r s0 boolT r).
        constructor.
  ------- reflexivity.
          Unshelve.
          apply a.
          apply unify_aux_tsubst_l;
          auto.
  ------- rewrite tsubst_compose_tsubst_add_r.
          rewrite <- Heq2.
          symmetry.
          apply tsubst_add_r_absorbs.
          assumption.
  --- destruct (bool_as_bool_eq (TIdentFacts.eqb s0 s1)) as [Heq | Heq].
  ----- apply (H _ (unify_aux_eq (eq_refl)) _ s).
        assumption.
  ----- edestruct H as [r [Heq1 Heq2]].
  ------- apply (
            unify_aux_tsubst_l
              (x := s0)
              (t := tvarT s1)
              (q := p)
          );
          auto.
  ------- apply par_tsubst_tsubst_solves.
  --------- exact H2.
  --------- assumption.
  ------- exists (tsubst_add_r s0 (tvarT s1) r).
          constructor.
  --------- rewrite Heq1.
            reflexivity.
            Unshelve.
            apply a.
            apply unify_aux_tsubst_l;
            auto.
  --------- rewrite tsubst_compose_tsubst_add_r.
            rewrite <- Heq2.
            symmetry.
            apply tsubst_add_r_absorbs.
            assumption.
  --- have Heq : occurs s0 (u1 ->T u2) = false.
  ----- apply (par_tsubst_nooccur H2).
        discriminate.
  ----- simpl in Heq.
        destruct (bool_as_bool_eq (occurs s0 u1 || occurs s0 u2)) as [Heq2 | Heq2].
  ------- rewrite Heq in Heq2.
          discriminate Heq2.
  ------- edestruct H as [r [Heq3 Heq4]].
  --------- apply (
            unify_aux_tsubst_l
              (x := s0)
              (t := u1 ->T u2)
              (q := p)
            );
            auto.
  --------- apply par_tsubst_tsubst_solves.
  ----------- exact H2.
  ----------- assumption.
  --------- exists (tsubst_add_r s0 (u1 ->T u2) r).
            constructor.
  ----------- rewrite Heq3.
              reflexivity.
              Unshelve.
              apply a.
              apply unify_aux_tsubst_l;
              auto.
  ----------- rewrite tsubst_compose_tsubst_add_r.
              rewrite <- Heq4.
              symmetry.
              apply tsubst_add_r_absorbs.
              assumption.
  --- have Heq : occurs s0 (u1 *T u2) = false.
  ----- apply (par_tsubst_nooccur H2).
        discriminate.
  ----- simpl in Heq.
        destruct (
          bool_as_bool_eq (occurs s0 u1 || occurs s0 u2)
        ) as [Heq2 | Heq2].
  ------- rewrite Heq in Heq2.
          discriminate Heq2.
  ------- edestruct H as [r [Heq3 Heq4]].
  --------- apply (
            unify_aux_tsubst_l
              (x := s0)
              (t := u1 *T u2)
              (q := p)
            );
            auto.
  --------- apply par_tsubst_tsubst_solves.
  ----------- exact H2.
  ----------- assumption.
  --------- exists (tsubst_add_r s0 (u1 *T u2) r).
            constructor.
  ----------- rewrite Heq3.
              reflexivity.
              Unshelve.
              apply a.
              apply unify_aux_tsubst_l;
              auto.
  ----------- rewrite tsubst_compose_tsubst_add_r.
              rewrite <- Heq4.
              symmetry.
              apply tsubst_add_r_absorbs.
              assumption.
  --- symmetry in H2.
      have Heq : occurs s0 (t1 ->T t2) = false.
  ----- apply (par_tsubst_nooccur H2).
        discriminate.
  ----- simpl in Heq.
        destruct (
          bool_as_bool_eq (occurs s0 t1 || occurs s0 t2)
        ) as [Heq2 | Heq2].
  ------- rewrite Heq in Heq2.
          discriminate Heq2.
  ------- edestruct H as [r [Heq3 Heq4]].
  --------- apply (
            unify_aux_tsubst_r
              (x := s0)
              (t := t1 ->T t2)
              (q := p)
            );
            auto.
  --------- apply par_tsubst_tsubst_solves.
  ----------- exact H2.
  ----------- assumption.
  --------- exists (tsubst_add_r s0 (t1 ->T t2) r).
            constructor.
  ----------- rewrite Heq3.
              reflexivity.
              Unshelve.
              apply a.
              apply unify_aux_tsubst_r;
              auto.
  ----------- rewrite tsubst_compose_tsubst_add_r.
              rewrite <- Heq4.
              symmetry.
              apply tsubst_add_r_absorbs.
              assumption.
  --- apply (H _ (unify_aux_funT (eq_refl)) _ s).
      right.
  ----- assumption.
  ----- right;
        assumption.
  --- symmetry in H2.
      have Heq : occurs s0 (t1 ->T t2) = false.
  ----- apply (par_tsubst_nooccur H2).
        discriminate.
  ----- simpl in Heq.
        destruct (
          bool_as_bool_eq (occurs s0 t1 || occurs s0 t2)
        ) as [Heq2 | Heq2].
  ------- rewrite Heq in Heq2.
          discriminate Heq2.
  ------- edestruct H as [r [Heq3 Heq4]].
  --------- apply (
            unify_aux_tsubst_r
              (x := s0)
              (t := t1 *T t2)
              (q := p)
            );
            auto.
  --------- apply par_tsubst_tsubst_solves.
  ----------- exact H2.
  ----------- assumption.
  --------- exists (tsubst_add_r s0 (t1 *T t2) r).
            constructor.
  ----------- rewrite Heq3.
              reflexivity.
              Unshelve.
              apply a.
              apply unify_aux_tsubst_r;
              auto.
  ----------- rewrite tsubst_compose_tsubst_add_r.
              rewrite <- Heq4.
              symmetry.
              apply tsubst_add_r_absorbs.
              assumption.
    --- apply (H _ (unify_aux_prodT (eq_refl)) _ s).
        right.
    ----- assumption.
    ----- right;
          assumption.
Qed.

Theorem unify_sound
  {p : unification_problem} {s : TMap.t typeT} :
    unify p = ok s -> solves s p.
Proof.
  exact unify_aux_sound.
Qed.

Theorem unify_complete_1
  {p : unification_problem} {s : TMap.t typeT} :
    solves s p -> exists r : TMap.t typeT, unify p = ok r.
Proof.
  move=> Hsol.
  destruct (
    unify_aux_complete
      (ACC := wf_unification_problem_order p) Hsol
  ) as [r [Heq1 _]].
  eauto.
Qed.

Theorem unify_complete_2
  {p : unification_problem} {r s : TMap.t typeT} :
    solves s p -> unify p = ok r -> r >>< s.
Proof.
  move=> Hsol Heq1.
  destruct (
    unify_aux_complete
      (ACC := wf_unification_problem_order p) Hsol
  ) as [q [Heq2 Heq3]].
  exists s.
  unfold unify in Heq1.
  rewrite Heq1 in Heq2.
  inversion Heq2.
  assumption.
Qed.
