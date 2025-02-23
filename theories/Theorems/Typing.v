Require Import Definitions.Ident.
Require Import Definitions.Type.
Require Import Definitions.Term.
Require Import Definitions.Typing.
Require Import Definitions.Context.
Require Import Theorems.Context.
Require Import Theorems.Substitution.
Require Import Theorems.Type.

Require Import List.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

(** Proof of specification of type-checking.
*)

Lemma derivation_context_order_with_tsubst
  {G H : Context.t} {e : termT} {t : typeT} {s : TMap.t typeT} :
    G >><c(s) H -> G |- e :T t -> H |- e :T t >> s.
Proof.
  move=> [Hbmap Hfmap] D.
  move: H Hbmap Hfmap.
  induction D;
  eauto using derivation;
  simpl.
  - move=> I Hbmap Hfmap.
    rewrite par_tsubst_par_tsubst.
    apply fvarT_ax.
    auto.
  - move=> H Hbmap Hfmap.
    apply absT_in.
    have Htsubst : G >><c(s) H.
    constructor;
    auto.
    rewrite (context_order_with_tsubst_bpush (t := t)) in Htsubst.
    apply IHD;
    auto.
    unfold bMapsTo.
    destruct n;
    simpl;
    move=> v Heq.
  --- inversion Heq.
      reflexivity.
  --- apply Hbmap.
      assumption.
Qed.

Lemma derivation_no_context_derivation
  {G : Context.t} {e : termT} {t : typeT} :
    |- e :T t -> G |- e :T t.
Proof.
  rewrite <- (par_tsubst_empty (@TMap.empty_1 _)) at -1.
  apply derivation_context_order_with_tsubst.
  exact empty_context_order_with_tsubst.
Qed.

Definition empty_fmap (G : Context.t) : Context.t :=
  {{ Context.bmap G, FMap.empty typeT}}.

Lemma derivation_bound_nclosed
  {G : Context.t} {e : termT} {t : typeT} :
    G |- e :T t -> bound_nclosed (length (bmap G)) e.
Proof.
  move=> Hderiv.
  induction Hderiv;
  eauto using bound_nclosed.
  apply bvarT_closed.
  unfold bMapsTo in H.
  apply nth_error_split in H.
  destruct H as [k [l [Heq1 Heq2]]].
  rewrite Heq1.
  rewrite app_length.
  simpl.
  Lia.lia.
Qed.

Lemma empty_derivation_bound_closed {e : termT} {t : typeT} :
    |- e :T t -> bound_closed e.
Proof.
  unfold bound_closed.
  change O with (length (Context.bmap Context.empty)).
  exact derivation_bound_nclosed.
Qed.

Lemma derivation_par_fsubst
  {G : Context.t} {s : FMap.t termT} {e : termT} {t : typeT} :
    (forall (x : FIdent.t) (t : typeT), Context.fMapsTo x t G ->
      exists e : termT,
        FMap.MapsTo x e s /\ |- e :T t) ->
    G |- e :T t ->
    empty_fmap G |- par_fsubst s e :T t.
Proof.
  move=> Hsub Hderiv.
  move: s Hsub.
  induction Hderiv;
  move=> r Hsub;
  simpl;
  eauto using derivation.
  - unfold fMapsTo in H.
    destruct (Hsub x t H) as [e [Hmap Hderiv]].
    rewrite (FMap.find_1 Hmap).
    move: Hderiv.
    apply derivation_context_order_with_tsubst.
    exact empty_context_order_with_tsubst.
  - apply absT_in.
    apply IHHderiv.
    move=> x v Hmap1.
    unfold bpush in Hmap1.
    unfold fMapsTo in Hmap1.
    simpl in Hmap1.
    destruct (Hsub x v Hmap1) as [f [Hmap2 Hderivf]].
    exists (bshift O f).
    constructor.
  --- auto using FMap.map_1.
  --- rewrite bound_closed_bshift;
      eauto using empty_derivation_bound_closed.
Qed.

Lemma build_unification_problem_sound
  {G : Context.t} {p : unification_problem} {s : TMap.t typeT}
  {used_tvars new_used_tvars : list TIdent.t} {e : termT} :
    build_unification_problem used_tvars G e =
    Some (p, new_used_tvars) -> solves s p ->
    G >>c s |- e :T tvarT (TIdent.new used_tvars) >> s.
Proof.
  move: G p s used_tvars new_used_tvars.
  induction e;
  move=> G p r used_tvars new_used_tvars Heq Hsol;
  simpl in Heq;
  simpl; [
    destruct (FMap.find s (fmap G)) eqn:Heq2;
    simpl in Heq |
    destruct (List.nth_error (bmap G) n) eqn:Heq2;
    simpl in Heq | ..
  ];
  try (
    inversion Heq as [Heq3];
    rewrite <- Heq3 in Hsol;
    inversion Hsol as [ H1 | [x l] q Huni Hfor];
    simpl in Huni;
    unfold unifies in Huni;
    simpl in Huni;
    rewrite Huni;
    eauto using derivation
  ); [
    rewrite par_tsubst_par_tsubst;
    apply fvarT_ax;
    unfold fMapsTo;
    simpl;
    apply FMap.find_2;
    assumption |
    apply bvarT_ax;
    unfold bMapsTo;
    simpl;
    rewrite List.nth_error_map;
    rewrite Heq2;
    reflexivity | ..
  ].
  - destruct (
      build_unification_problem
        (TIdent.new (TIdent.new used_tvars :: used_tvars) ::
        TIdent.new used_tvars :: used_tvars)
        (bpush
          (tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)))
          G) 
        e
    ) eqn:Heq2;
    try destruct p0 as [p' used_tvars'];
    simpl in Heq;
    inversion Heq as [Heq3];
    rewrite <- Heq3 in Hsol.
    inversion Hsol as [ H1 | [x l] q Huni Hfor].
    simpl in Huni.
    unfold unifies in Huni.
    simpl (tvarT (TIdent.new used_tvars) >> r) in Huni.
    rewrite Huni.
    apply absT_in.
    fold (tvarT ((TIdent.new
        (TIdent.new (TIdent.new used_tvars :: used_tvars)
          :: TIdent.new used_tvars :: used_tvars))) >> r).
    fold (tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)) >> r).
    rewrite <- context_par_tsubst_bpush.
    eapply IHe.
    exact Heq2.
    assumption.
  - destruct (
      build_unification_problem 
        (TIdent.new used_tvars :: used_tvars) G e1
    ) eqn:Heq2;
    try destruct p0 as [p_fun used_tvars_fun];
    simpl in Heq;
    inversion Heq as [Heq3];
    destruct (build_unification_problem used_tvars_fun G e2) eqn:Heq4;
    try destruct p0 as [p_arg used_tvars_arg];
    simpl in Heq3;
    inversion Heq3 as [Heq5];
    rewrite <- Heq5 in Hsol.
    inversion Hsol as [ H1 | [x l] q Huni Hfor].
    rewrite Forall_app in Hfor.
    destruct Hfor as [Hfor_arg Hfor_fun].
    simpl in Huni.
    unfold unifies in Huni.
    simpl in Huni;
    fold (tvarT (TIdent.new used_tvars) >> r) in Huni;
    fold (tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)) >> r) in Huni;
    fold (tvarT (TIdent.new used_tvars_fun) >> r) in Huni.
    apply (appT_el _ _ _ (tvarT (TIdent.new used_tvars_fun) >> r));
    try fold (tvarT (TIdent.new used_tvars) >> r);
    try rewrite <- Huni;
    eauto.
  - destruct (
      build_unification_problem 
        (TIdent.new used_tvars :: used_tvars) G e1
    ) eqn:Heq2;
    try destruct p0 as [p_left used_tvars_left];
    simpl in Heq;
    inversion Heq as [Heq3];
    destruct (build_unification_problem used_tvars_left G e2) eqn:Heq4;
    try destruct p0 as [p_right used_tvars_right];
    simpl in Heq3;
    inversion Heq3 as [Heq5];
    rewrite <- Heq5 in Hsol.
    inversion Hsol as [ H1 | [x l] q Huni Hfor].
    rewrite Forall_app in Hfor.
    destruct Hfor as [Hfor_right Hfor_left].
    simpl in Huni.
    unfold unifies in Huni.
    simpl in Huni.
    rewrite Huni.
    clear Huni.
    fold (tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)) >> r);
    fold (tvarT (TIdent.new used_tvars_left) >> r).
    eauto using derivation.
  - destruct (
      build_unification_problem
        (TIdent.new (TIdent.new used_tvars :: used_tvars)
        :: TIdent.new used_tvars :: used_tvars) G e
    ) eqn:Heq2;
    try destruct p0 as [p_left used_tvars_left];
    simpl in Heq;
    inversion Heq as [Heq3];
    rewrite <- Heq3 in Hsol.
    inversion Hsol as [ H1 | [x l] q Huni Hfor].
    unfold unifies in Huni.
    simpl in Huni;
    fold (
      tvarT
        (TIdent.new
          (TIdent.new (TIdent.new used_tvars :: used_tvars) ::
          TIdent.new used_tvars :: used_tvars)) >> r
    ) in Huni;
    fold (tvarT (TIdent.new used_tvars) >> r) in Huni;
    fold (
      tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)) >> r
    ) in Huni.
    fold (tvarT (TIdent.new used_tvars) >> r).
    apply (plT_el _ _ _ (tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)) >> r)).
    rewrite <- Huni.
    eauto.
  - destruct (
      build_unification_problem
        (TIdent.new (TIdent.new used_tvars :: used_tvars)
        :: TIdent.new used_tvars :: used_tvars) G e
    ) eqn:Heq2;
    try destruct p0 as [p_left used_tvars_right];
    simpl in Heq;
    inversion Heq as [Heq3];
    rewrite <- Heq3 in Hsol.
    inversion Hsol as [ H1 | [x l] q Huni Hfor].
    unfold unifies in Huni.
    simpl in Huni;
    fold (
      tvarT
        (TIdent.new
          (TIdent.new (TIdent.new used_tvars :: used_tvars) ::
          TIdent.new used_tvars :: used_tvars)) >> r
    ) in Huni;
    fold (tvarT (TIdent.new used_tvars) >> r) in Huni;
    fold (
      tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)) >> r
    ) in Huni.
    fold (tvarT (TIdent.new used_tvars) >> r).
    apply (prT_el _ _ (tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)) >> r)).
    rewrite <- Huni.
    eauto.
  - destruct (
      build_unification_problem 
        (TIdent.new used_tvars :: used_tvars) G e1
    ) eqn:Heq2;
    try destruct p0 as [p_if used_tvars_if];
    simpl in Heq;
    inversion Heq as [Heq3];
    destruct (build_unification_problem used_tvars_if G e2) eqn:Heq4;
    try destruct p0 as [p_then used_tvars_then];
    simpl in Heq3;
    inversion Heq3 as [Heq5];
    destruct (build_unification_problem used_tvars_then G e3) eqn:Heq6;
    try destruct p0 as [p_else used_tvars_else];
    simpl in Heq5;
    inversion Heq5 as [Heq7];
    rewrite <- Heq7 in Hsol.
    inversion Hsol as [ _H1 | [x y] q Huni1 Hfor1].
    inversion Hfor1 as [ _H1 | [z w] o Huni2 Hfor2].
    inversion Hfor2 as [ _H1 | [v u] n Huni3 Hfor3].
    repeat rewrite Forall_app in Hfor3.
    destruct Hfor3 as [Hfor_else [Hfor_then Hfor_if]].
    unfold unifies in Huni1, Huni2, Huni3;
    simpl fst in Huni1, Huni2, Huni3;
    simpl snd in Huni1, Huni2, Huni3.
    fold (tvarT (TIdent.new used_tvars) >> r).
    rewrite Huni1.
    apply iteT_el;
    fold (boolT >> r);
    eauto;
    try rewrite <- Huni3;
    try rewrite Huni2;
    eauto.
  - destruct (
      build_unification_problem
        (TIdent.new used_tvars :: used_tvars) G e
    ) eqn:Heq2;
    try destruct p0 as [p_if used_tvars_if];
    simpl in Heq;
    inversion Heq as [Heq3];
    clear Heq.
    rewrite <- Heq3 in Hsol.
    inversion Hsol as [ _H1 | [x y] q Huni1 Hfor1].
    inversion Hfor1 as [ _H1 | [z w] o Huni2 Hfor2].
    unfold unifies in Huni1, Huni2;
    simpl fst in Huni1, Huni2;
    simpl snd in Huni1, Huni2.
    fold (tvarT (TIdent.new used_tvars) >> r).
    rewrite Huni1.
    apply sT_el.
    fold (natT >> r).
    rewrite <- Huni2.
    eauto.
    - destruct (
      build_unification_problem 
        (TIdent.new used_tvars :: used_tvars) G e1
    ) eqn:Heq2;
    try destruct p0 as [p_base used_tvars_base];
    simpl in Heq;
    inversion Heq as [Heq3];
    destruct (build_unification_problem used_tvars_base G e2) eqn:Heq4;
    try destruct p0 as [p_rec used_tvars_rec];
    simpl in Heq3;
    inversion Heq3 as [Heq5];
    destruct (build_unification_problem used_tvars_rec G e3) eqn:Heq6;
    try destruct p0 as [p_arg used_tvars_arg];
    simpl in Heq5;
    inversion Heq5 as [Heq7];
    rewrite <- Heq7 in Hsol.
    inversion Hsol as [ _H1 | [x y] q Huni1 Hfor1].
    inversion Hfor1 as [ _H1 | [z w] o Huni2 Hfor2].
    inversion Hfor2 as [ _H1 | [v u] n Huni3 Hfor3].
    repeat rewrite Forall_app in Hfor3.
    destruct Hfor3 as [Hfor_arg [Hfor_rec Hfor_base]].
    unfold unifies in Huni1, Huni2, Huni3;
    simpl in Huni1, Huni2, Huni3;
    rewrite Huni1.
    apply recT_el.
  --- eauto.
  --- simpl.
      rewrite <- Huni3.
      fold (tvarT (TIdent.new used_tvars_base) >> r).
      eauto.
  --- rewrite <- Huni2.
      eauto.
Qed.

Theorem type_check_sound {tenv : FMap.t typeT} {e : termT} {t : typeT} :
    type_check tenv e = ok t -> {{nil, tenv}} |- e :T t.
Proof.
  move=> Heq1.
  unfold type_check in Heq1.
  destruct (
    build_unification_problem nil {{nil, tenv}} e
  ) as [[p used_tvars] | ] eqn:Heq2;
  try (
    inversion Heq1;
    fail
  ).
  destruct (
    Unification.unify p
  ) as [s | ] eqn:Heq3;
  inversion  Heq1 as [Heq4].
  apply (build_unification_problem_sound (s := s)) in Heq2;
  auto using Unification.unify_sound.
Qed.

Definition TMap_inclusion {A : Type} (r s : TMap.t A) : Prop :=
  forall (x : TIdent.t) (a : A), TMap.MapsTo x a r ->
  TMap.MapsTo x a s.

Notation "r <=m s" := (TMap_inclusion r s) (at level 50). 

Definition TMap_agree {A : Type} (r s : TMap.t A) : Prop :=
  forall (x : TIdent.t) (a b : A),
  TMap.MapsTo x a r -> TMap.MapsTo x b s ->
  a = b.

Definition TMap_left_union {A : Type} (r s : TMap.t A) : TMap.t A :=
  TMap.map2
    (fun opt1 opt2 =>
      match opt1, opt2 with
      | Some x, _
      | _, Some x => Some x
      | _, _ => None
      end)
    r s.

Lemma TMap_left_union_spec_1 {A : Type} {r s : TMap.t A} :
    r <=m (TMap_left_union r s).
Proof.
  move=> x a Hmap.
  apply TMap.find_2.
  rewrite TMapFacts.map2_1bis;
  try reflexivity.
  rewrite (TMap.find_1 (e := a));
  auto.
Qed.

Lemma TMap_left_union_spec_2 {A : Type} {r s : TMap.t A} :
    TMap_agree r s ->
    s <=m (TMap_left_union r s).
Proof.
  move=> Hagr x a Hmap.
  apply TMap.find_2.
  rewrite TMapFacts.map2_1bis;
  try reflexivity.
  destruct (TMap.find x r) eqn:Heq.
  - rewrite (Hagr x a0 a);
    auto.
    apply TMap.find_2.
    assumption.
  - rewrite (TMap.find_1 (e := a));
    auto.
Qed.

Lemma TMap_left_union_spec_3
  {A : Type} {r s : TMap.t A} {x : TIdent.t} {a : A} :
  TMap.MapsTo x a (TMap_left_union r s) ->
  TMap.MapsTo x a r \/ TMap.MapsTo x a s.
Proof.
  move=> Hmap.
  apply TMap.find_1 in Hmap.
  rewrite TMapFacts.map2_1bis in Hmap;
  try reflexivity.
  destruct (TMap.find x r) eqn:Heq1.
  - left.
    inversion Hmap.
    rewrite H0 in Heq1.
    auto using TMap.find_2.
  - right.
    destruct (TMap.find x s) eqn:Heq2;
    inversion Hmap.
    rewrite H0 in Heq2.
    auto using TMap.find_2.
Qed.

Lemma TMap_inclusion_par_tsubst_1 {r s : TMap.t typeT} {t : typeT} :
    r <=m s ->
    (forall x : TIdent.t, TSet.In x (variable_set t) ->
      TMap.In x s ->
      TMap.In x r) ->
    t >> s = t >> r.
Proof.
  move=> Hcomp Hin.
  induction t;
  simpl;
  simpl in Hin;
  auto;
  try (
    f_equal;
    try apply IHt1;
    try apply IHt2;
    move=> x Hin1 Hin2;
    apply Hin;
    try TSetFacts.fsetdec;
    assumption
  ).
  destruct (TMap.find n r) eqn:Heq1.
  - apply (TMap.find_2) in Heq1.
    apply Hcomp in Heq1.
    rewrite (TMap.find_1 Heq1).
    reflexivity.
  - destruct (TMap.find n s) eqn:Heq2;
    try reflexivity.
    apply (TMap.find_2) in Heq2.
    have foo : TMap.In n r.
  --- apply Hin.
  ----- TSetFacts.fsetdec.
  ----- exists t.
        assumption.
  --- rewrite <- TMapFacts.not_find_in_iff in Heq1.
      contradiction.
Qed.

Lemma TMap_inclusion_par_tsubst_2 {r s : TMap.t typeT} {t : typeT} :
    r <=m s ->
    (forall x : TIdent.t, TSet.In x (variable_set t) ->
      TMap.In x r) ->
    t >> s = t >> r.
Proof.
  auto using TMap_inclusion_par_tsubst_1.
Qed.

Lemma TMap_inclusion_unifies {r s : TMap.t typeT} {t u : typeT} :
    r <=m s ->
    (forall x : TIdent.t, TSet.In x (variable_set t) ->
      TMap.In x r) ->
    (forall x : TIdent.t, TSet.In x (variable_set u) ->
      TMap.In x r) ->
    unifies r t u ->
    unifies s t u.
Proof.
  move=> Hcomp Hin1 Hin2 Huni.
  unfold unifies.
  repeat rewrite (TMap_inclusion_par_tsubst_2 (r := r));
  auto.
Qed.

Lemma TMap_inclusion_solves
  {r s : TMap.t typeT} {p : unification_problem} :
    r <=m s ->
    (forall x : TIdent.t, TSet.In x (problem_variable_set p) ->
      TMap.In x r) ->
    solves r p ->
    solves s p.
Proof.
  move=> Hcomp Hin1 Hsol.
  induction Hsol as [ | [t u] p];
  try left;
  try right;
  simpl;
  simpl in Hin1.
  - apply (TMap_inclusion_unifies (r := r));
    auto;
    move=> x Hin2;
    apply Hin1;
    TSetFacts.fsetdec.
  - apply IHHsol.
    move=> x Hin2;
    apply Hin1;
    TSetFacts.fsetdec.
Qed.

Lemma TMap_left_union_solves_l
  {r s : TMap.t typeT} {p : unification_problem} :
    (forall x : TIdent.t, TSet.In x (problem_variable_set p) ->
      TMap.In x r) ->
    solves r p ->
    solves (TMap_left_union r s) p.
Proof.
  eauto using TMap_inclusion_solves, TMap_left_union_spec_1.
Qed.

Lemma TMap_left_union_solves_r
  {r s : TMap.t typeT} {p : unification_problem} :
    TMap_agree r s ->
    (forall x : TIdent.t, TSet.In x (problem_variable_set p) ->
      TMap.In x s) ->
    solves s p ->
    solves (TMap_left_union r s) p.
Proof.
  eauto using TMap_inclusion_solves, TMap_left_union_spec_2.
Qed.

Lemma build_unification_problem_used_tvars_inc
  {used_tvars new_used_tvars : list TIdent.t}
  {G : Context.t} {p : unification_problem} {e : termT}
  {x : TIdent.t} :
  build_unification_problem used_tvars G e =
  Some (p, new_used_tvars) -> In x used_tvars ->
  In x new_used_tvars.
Proof.
  move: used_tvars new_used_tvars G p x.
  induction e;
  simpl;
  move=> used_tvars new_used_tvars G p x Heq1 Hin; [
    destruct (FMap.find s (fmap G)) |
    destruct (nth_error (bmap G) n) |
    .. 
  ];
  try (
    simpl in Heq1;
    inversion Heq1;
    eauto using in_cons, in_or_app;
    fail
  );
  try (
    destruct (
      build_unification_problem
        (TIdent.new (TIdent.new used_tvars :: used_tvars)
        :: TIdent.new used_tvars :: used_tvars) G e
    ) eqn:Heq2;
    try destruct p0 as [p_1 used_tvars_1];
    simpl in Heq1;
    inversion Heq1 as [Heq3];
    rewrite <- H;
    eauto using in_cons, in_or_app;
    fail
  );
  try (
    destruct (
      build_unification_problem 
        (TIdent.new used_tvars :: used_tvars) G e1
    ) eqn:Heq2;
    try destruct p0 as [p_1 used_tvars_1];
    simpl in Heq1;
    inversion Heq1 as [Heq3];
    destruct (build_unification_problem used_tvars_1 G e2) eqn:Heq4;
    try destruct p0 as [p_2 used_tvars_2];
    simpl in Heq3;
    inversion Heq3 as [Heq5];
    try (
      destruct (build_unification_problem used_tvars_2 G e3) eqn:Heq6;
      try destruct p0 as [p_3 used_tvars_3];
      simpl in Heq5;
      inversion Heq5 as [Heq7];
      rewrite <- H;
      eauto using in_cons, in_or_app;
      fail
    );
    rewrite <- H;
    eauto using in_cons, in_or_app;
    fail
  ).
  - destruct (
      build_unification_problem
        (TIdent.new (TIdent.new used_tvars :: used_tvars) ::
        TIdent.new used_tvars :: used_tvars)
        (bpush
          (tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars)))
          G) 
        e
    ) eqn:Heq2;
    try destruct p0 as [p' used_tvars'];
    simpl in Heq1;
    inversion Heq1.
    rewrite <- H1;
    eauto using in_cons, in_or_app.
  - destruct (
      build_unification_problem 
        (TIdent.new used_tvars :: used_tvars) G e
    ) eqn:Heq2;
    try destruct p0 as [p' used_tvars'];
    simpl in Heq1;
    inversion Heq1.
    rewrite <- H1;
    eauto using in_cons, in_or_app.
Qed.

Lemma par_tsubst_add {s : TMap.t typeT} {x : TIdent.t} {t u : typeT} :
    ~TSet.In x (variable_set t) ->
    t >> (TMap.add x u s) = t >> s.
Proof.
  move: s x u.
  induction t;
  simpl;
  move=> s x u Hnin;
  auto;
  try (
    f_equal;
    try apply IHt1;
    try apply IHt2;
    TSetFacts.fsetdec
  ).
  simpl in Hnin.
  rewrite TSetFacts.singleton_iff in Hnin.
  rewrite TMapFacts.add_neq_o;
  auto.
Qed.

Lemma context_par_tsubst_add
  {G : Context.t}
  {s : TMap.t typeT} {x : TIdent.t} {t : typeT} :
    ~ TSet.In x (context_tvarT_set G) ->
    G >>c (TMap.add x t s) = G >>c s.
Proof.
  destruct G.
  move: s x t fmap.
  induction bmap;
  simpl;
  move=> s x t fmap Hnin;
  auto.
  unfold ">>c".
  simpl.
  unfold ">>c" in IHbmap.
  simpl in IHbmap.
  unfold context_tvarT_set in Hnin.
  simpl in Hnin.
  replace (fold_right (fun t : typeT => [eta TSet.union (variable_set t)]) TSet.empty
  bmap) with (context_tvarT_set {{bmap, fmap}}) in Hnin;
  try reflexivity.
  f_equal.
  f_equal.
  - apply par_tsubst_add.
    TSetFacts.fsetdec.
  - have Hnin2 : ~ TSet.In x (context_tvarT_set {{bmap, fmap}}).
    TSetFacts.fsetdec.
    have Heq := IHbmap s x t fmap Hnin2.
    inversion Heq.
    reflexivity.
Qed.

Lemma unification_problem_solves_add
  {p : unification_problem}
  {s : TMap.t typeT} {x : TIdent.t} {t : typeT} :
    ~ TSet.In x (problem_variable_set p) ->
    solves s p -> solves (TMap.add x t s) p.
Proof.
  move: s x t.
  induction p;
  simpl;
  move=> s x t Hnin Hsol1;
  auto.
  - left.
  - inversion Hsol1 as [ | [u v] Heq1 Hsol2].
    simpl in Hsol2.
    rewrite <- H0 in Hnin.
    right.
  --- unfold unifies.
      simpl.
      repeat rewrite par_tsubst_add;
      try TSetFacts.fsetdec.
      assumption.
  --- apply IHp.
      TSetFacts.fsetdec.
      assumption. 
Qed.

Lemma build_unification_problem_complete_1
  {used_tvars : list TIdent.t}
  {G H : Context.t} {s : TMap.t typeT}
  {e : termT} {t : typeT} :
    H = G >>c s ->
    (forall x : TIdent.t,
      TSet.In x (context_tvarT_set G) ->
      In x used_tvars) ->
    H |- e :T t ->
    exists (p : unification_problem) (new_used_tvars : list TIdent.t),
    build_unification_problem used_tvars G e =
    Some (p, new_used_tvars).
Proof.
  move=> Heq1 Htvars Hderiv.
  move: G s used_tvars Heq1 Htvars.
  induction Hderiv;
  move=> I r used_tvars Heq1 Htvars;
  simpl;
  eauto;
  try (
    destruct (
      IHHderiv1 I r (TIdent.new used_tvars :: used_tvars)
    ) as [p_1 [used_tvars_1 Heq_1]];
    try right;
    auto;
    rewrite Heq_1;
    destruct (
      IHHderiv2 I r used_tvars_1
    ) as [p_2 [used_tvars_2 Heq_2]];
    try right;
    auto; [
      move=> x Hin;
      apply (build_unification_problem_used_tvars_inc Heq_1);
      right;
      eauto |
      rewrite Heq_2;
      try (
        destruct (IHHderiv3 I r used_tvars_2) as [p_3 [used_tvars_3 Heq_3]];
        try right;
        auto; [
        move=> x Hin;
        apply (build_unification_problem_used_tvars_inc Heq_2);
        apply (build_unification_problem_used_tvars_inc Heq_1);
        right;
        eauto |
        rewrite Heq_3;
        eauto
      ];
      fail
      );
      eauto
    ];
    fail
  );
  try (
    destruct (
      IHHderiv
        I r (TIdent.new (TIdent.new used_tvars :: used_tvars) :: TIdent.new used_tvars :: used_tvars)
    ) as [p [new_used_tvars Heq]];
    eauto using in_cons, in_or_app;
    rewrite Heq;
    eauto;
    fail
  ).
  - rewrite Heq1 in H.
    unfold bMapsTo in H.
    simpl in H.
    rewrite nth_error_map in H.
    destruct (nth_error (bmap I) n);
    inversion H.
    simpl.
    eauto.
  - unfold fMapsTo in H.
    rewrite Heq1 in H.
    simpl in H.
    rewrite (FMap.find_1 (e := t));
    simpl;
    eauto.
  - destruct (
      IHHderiv
        (bpush (tvarT (TIdent.new (TIdent.new used_tvars :: used_tvars))) I)
        (TMap.add (TIdent.new (TIdent.new used_tvars :: used_tvars)) t r)
        (TIdent.new (TIdent.new used_tvars :: used_tvars) :: TIdent.new used_tvars :: used_tvars)
    ) as [p [new_used_tvars Heq]].
  --- rewrite context_par_tsubst_bpush.
      simpl.
      rewrite TMapFacts.add_eq_o;
      try reflexivity.
      rewrite context_par_tsubst_add.
  ----- move=> Hin.
        apply (
          TIdent.new_spec (l := TIdent.new used_tvars :: used_tvars)
        ).
        right.
        auto.
  ----- rewrite Heq1.
        reflexivity. 
  --- unfold bpush.
      unfold context_tvarT_set.
      simpl.
      fold (context_tvarT_set I).
      move=> x Hin.
      apply TSet.union_1 in Hin.
      destruct Hin as [Hin | Hin];
      try apply TSet.singleton_1 in Hin;
      eauto.
  --- rewrite Heq.
      eauto.
  - destruct (
      IHHderiv I r (TIdent.new used_tvars :: used_tvars)
    ) as [p_1 [used_tvars_1 Heq_1]];
    try right;
    eauto.
    rewrite Heq_1.
    eauto.
Qed.

Lemma tvarT_set_context_tvarT_set {G : Context.t} {n : nat} {t : typeT}
  {x : TIdent.t} :
    bMapsTo n t G -> TSet.In x (variable_set t) ->
    TSet.In x (context_tvarT_set G).
Proof.
  destruct G.
  move: fmap n t x.
  induction bmap;
  move=> fmap n t x Hmap Hin.
  - unfold bMapsTo in Hmap.
    simpl in Hmap.
    destruct n;
    discriminate Hmap.
  - unfold bMapsTo in Hmap.
    destruct n.
  --- simpl in Hmap.
      inversion Hmap.
      unfold context_tvarT_set.
      simpl.
      apply TSet.union_2.
      assumption.
  --- simpl in Hmap.
      unfold context_tvarT_set.
      simpl.
      replace (
        fold_right
          (fun t : typeT => [eta TSet.union (variable_set t)])
          TSet.empty
          bmap
      ) with (context_tvarT_set {{bmap, fmap}});
      try reflexivity.
      apply TSet.union_3.
      apply (IHbmap fmap n t);
      auto.
Qed.

Lemma build_unification_problem_complete_2
  {p : unification_problem} {used_tvars new_used_tvars : list TIdent.t}
  {s : TMap.t typeT} {G H : Context.t} {e : termT} {t : typeT} :
    build_unification_problem used_tvars G e =
    Some (p, new_used_tvars) ->
    H = G >>c s -> H |- e :T t ->
    (forall x : TIdent.t,
      TSet.In x (Context.context_tvarT_set G) ->
      In x used_tvars) ->
    exists r : TMap.t typeT,
      ((H = G >>c r /\
        (forall x : TIdent.t, TMap.In x r ->
          In x used_tvars ->
          TSet.In x (Context.context_tvarT_set G))) /\
        (forall x : TIdent.t, TMap.In x r ->
          In x new_used_tvars) /\
        (forall x : TIdent.t, TSet.In x (problem_variable_set p) ->
          TMap.In x r)) /\
        (forall x : TIdent.t, TSet.In x (Context.context_tvarT_set G) ->
          TMap.In x r) /\
        solves r p /\
        t = tvarT (TIdent.new used_tvars) >> r.
Proof.
Admitted.

Theorem type_check_complete_1
  {tenv : FMap.t typeT} {e : termT} {t : typeT} :
    {{nil, tenv}} |- e :T t ->
    exists (u : typeT), type_check tenv e = ok u.
Proof.
  move=> Hderiv.
  unfold type_check.
  destruct (
    build_unification_problem_complete_1
      (used_tvars := nil)
      (G := {{nil, tenv}})
      (H := {{nil, tenv}})
      (s := TMap.empty typeT)
      (e := e)
      (t := t)
  ) as [p [new_used_tvars Heq]];
  auto;
  try reflexivity;
  unfold context_tvarT_set;
  try apply TSet.empty_1.
  rewrite Heq.
  destruct (
    build_unification_problem_complete_2
      (p := p)
      (used_tvars := nil)
      (s := TMap.empty typeT)
      (new_used_tvars := new_used_tvars)
      (G := {{nil, tenv}})
      (H := {{nil, tenv}})
      (e := e)
      (t := t)
  ) as [s [[[Heq1 Hin1] _] [Hin2 [Hsol Heq2]]]];
  auto;
  try reflexivity;
  unfold context_tvarT_set;
  try apply TSet.empty_1.
  destruct (
    Unification.unify_complete_1
      (p := p)
      (s := s)
  ) as [r Heq3].
  assumption.
  rewrite Heq3.
  eauto.
Qed.

Theorem type_check_complete_2
  {tenv : FMap.t typeT} {e : termT} {G : Context.t} {t u : typeT} :
    {{nil, tenv}} |- e :T t ->
    type_check tenv e = ok u -> u >><t t.
Proof.
  move=> Hderiv Heq1.
  unfold type_check in Heq1.
  destruct (
    build_unification_problem_complete_1
      (used_tvars := nil)
      (G := {{nil, tenv}})
      (H := {{nil, tenv}})
      (s := TMap.empty typeT)
      (e := e)
      (t := t)
  ) as [p [new_used_tvars Heq2]];
  auto;
  try reflexivity;
  unfold context_tvarT_set;
  try apply TSet.empty_1.
  rewrite Heq2 in Heq1.
  destruct (
      build_unification_problem_complete_2
        (p := p)
        (used_tvars := nil)
        (new_used_tvars := new_used_tvars)
        (G := {{nil, tenv}})
        (H := {{nil, tenv}})
        (s := TMap.empty typeT)
        (e := e)
        (t := t)
    ) as [s [[[Heq3 _] _] [_ [Hsol Heq4]]]];
    auto;
    try reflexivity;
    unfold context_tvarT_set;
    try apply TSet.empty_1.
    destruct (
      Unification.unify_complete_1
        (p := p)
        (s := s)
    ) as [r Heq5].
    auto.
    rewrite Heq5 in Heq1.
    destruct (
      Unification.unify_complete_2
        (p := p)
        (r := r)
        (s := s)
    ) as [q Heq6];
    auto.
    exists q.
    inversion Heq1.
    fold (tvarT (TIdent.new nil) >> r).
    rewrite par_tsubst_par_tsubst.
    rewrite <- Heq6.
    assumption.
Qed.
