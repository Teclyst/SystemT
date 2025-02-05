Require Import Definitions.Ident.
Require Import Definitions.Type.
Require Import Definitions.Term.
Require Import Definitions.Typing.
Require Import Definitions.Context.
Require Import Theorems.Context.
Require Import Theorems.Type.

Require Import List.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

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
    destruct Htsubst as [Hbmap2 Hfmap2].
    apply IHD;
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

Lemma build_unification_problem_sound
  {G : Context.t} {p : unification_problem} {s : TMap.t typeT}
  {used_tvars new_used_tvars : list TIdent.t} {e : termT} :
    build_unification_problem used_tvars G e =
    Some (p, new_used_tvars) -> solves s p ->
    context_par_tsubst s G |- e :T tvarT (TIdent.new used_tvars) >> s.
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
