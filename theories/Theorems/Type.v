Require Import Definitions.Type.

Require Import List.

Require Import ssreflect ssrfun ssrbool.

Lemma par_tsubst_empty {s : TMap.t typeT} {t : typeT} :
    TMap.Empty s -> par_tsubst s t = t.
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
    par_tsubst h (par_tsubst s t) =
    par_tsubst (tsubst_compose s h) t.
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

Lemma par_tsubst_tsubst
  {s : TMap.t typeT} {x : TIdent.t} {t u : typeT} :
    (par_tsubst s (tsubst x t u)) =
    par_tsubst (tsubst_add_r x t s) u.
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

Lemma unify_aux_funT {t u v w : typeT} {p q : unification_problem} :
    p = (t ->T u, v ->T w) :: q ->
    unification_problem_order
      ((t, v) :: (u, w) :: q)
      p.
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
    unification_problem_order
      ((t, v) :: (u, w) :: q)
      p.
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

Lemma tsubst_subset {x : TIdent.t} {t u : typeT} :
    TSet.Subset (variable_set (tsubst x t u))
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

Lemma unify_aux_subset
  {x : TIdent.t} {t : typeT} {p :unification_problem} :
    TSet.Subset
      (problem_variable_set
        (List.map
          (fun c =>
            (tsubst x t (fst c), tsubst x t (snd c)))
          p))
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

Lemma unify_aux_nooccur
  {x : TIdent.t} {t : typeT} {p :unification_problem} :
    ~TSet.In x (variable_set t) ->
    ~TSet.In x
      (problem_variable_set
        (List.map
          (fun c =>
            (tsubst x t (fst c), tsubst x t (snd c)))
          p)).
Proof.
  move=> Hnooccur.
  induction p as [ | [u v] p];
  simpl.
  - TSetFacts.fsetdec.
  - have Hnooccur1 := @tsubst_preserves_nooccur x t u.
    have Hnooccur2 := @tsubst_preserves_nooccur x t v.
    TSetFacts.fsetdec.
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

Lemma unify_aux_tsubst_l
  {x : TIdent.t} {t : typeT} {p q : unification_problem} :
    occurs x t = false ->
    p = (tvarT x, t) :: q ->
    unification_problem_order
      ((List.map
        (fun c => (tsubst x t (fst c), tsubst x t (snd c)))
        q))
      p.
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
    unification_problem_order
      ((List.map
        (fun c => (tsubst x t (fst c), tsubst x t (snd c)))
        q))
      p.
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
          (List.map
            (fun c => (tsubst x t (fst c), tsubst x t (snd c)))
          q) (Acc_inv ACC (unify_aux_tsubst_l Heq2 Heq)))
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
          (List.map
            (fun c => (tsubst x t (fst c), tsubst x t (snd c)))
          q) (Acc_inv ACC (unify_aux_tsubst_l Heq2 Heq)))
    end
  | list_eq_cons _ (t, tvarT x) q Heq =>
    match bool_as_bool_eq (occurs x t) with
    | bool_eq_true _ _  => err (tvarT_occurs x t)
    | bool_eq_false _ Heq2 =>
      result_map
        (tsubst_add_r x t)
        (unify_aux
          (List.map
            (fun c => (tsubst x t (fst c), tsubst x t (snd c)))
          q) (Acc_inv ACC (unify_aux_tsubst_r Heq2 Heq)))
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
    solves s
      (map (fun c : typeT * typeT =>
        (tsubst x t c.1, tsubst x t c.2)) p) ->
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

Lemma unify_aux_correct_1
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

Lemma unify_aux_correct_2
  {p : unification_problem} {ACC : Acc unification_problem_order p}
  {s : TMap.t typeT} :
    solves s p -> exists r : TMap.t typeT, unify_aux p ACC = ok r.
Proof.
  move: s.
  induction p using (well_founded_induction wf_unification_problem_order);
  move=> s Hsol.
  destruct ACC.
  destruct p as [
    | [t u] p];
    simpl.
  - eauto.
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
Admitted.

Lemma unify_correct_1
  {p : unification_problem} {s : TMap.t typeT} :
    unify p = ok s -> solves s p.
Proof.
  exact unify_aux_correct_1.
Qed.
