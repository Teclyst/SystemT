Require Import Definitions.Ident.
Require Import Definitions.Type.
Require Import Definitions.Term.
Require Import Definitions.Reduction.
Require Import Definitions.Typing.
Require Import Theorems.Reduction.

Require Import PeanoNat.
Require Import List.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

(** Given a type substitution and a typing derivation, applying
    that substitution to the context and all types appearing in the
    derivation yields a new derivation.
*)
Lemma derivation_par_tsubst
  {G : Context.t} {e : termT} {t : typeT} {s : TMap.t typeT} :
    G |- e :T t ->
    Context.context_par_tsubst s G |- e :T typeT_par_tsubst s t.
Proof.
  intro D.
  induction D;
  eauto using derivation;
  simpl.
  - apply bvarT_ax.
    simpl.
    apply List.map_nth_error.
    exact H.
  - apply fvarT_ax.
    simpl.
    apply FMap.map_1.
    exact H.
Qed.

Fixpoint insert {A : Type} (n : nat) (x : A) (l : list A) :
    option (list A) :=
  match n, l with
  | O, _ => Some (x :: l)
  | _, nil => None
  | S n, a :: l =>
    option_map (cons a) (insert n x l)
  end.

Lemma insert_length {A : Type} (n : nat) (x : A) (l : list A) :
    (exists m : list A, insert n x l = Some m) <-> n <= length l.
Proof.
  move: n.
  induction l;
  move=> n;
  simpl.
  - constructor;
    intro H.
  --- destruct H as [m Hm].
      destruct n as [ | n];
      simpl in Hm.
  ----- auto.
  ----- discriminate Hm.
  --- rewrite Nat.le_0_r in H.
      rewrite H.
      simpl.
      exists (x :: nil).
      reflexivity.
  - constructor;
    intro H;
    destruct n as [ | n];
    simpl in H;
    simpl.
  --- exact (Nat.le_0_l _).
  --- destruct (insert n x l) as [m | ] eqn:Heq;
      try (
        simpl in H;
        destruct H as [m H];
        discriminate H
      ).
      apply le_n_S.
      rewrite <- IHl.
      exists m.
      exact Heq.
  --- eauto.
  --- apply le_S_n in H.
      rewrite <- IHl in H.
      destruct (insert n x l) as [m | ] eqn:Heq;
      try (
        simpl in H;
        destruct H as [m H];
        discriminate H
      ).
      simpl.
      eauto.
Qed.

Lemma insert_nth_err_lt {A : Type} {m n : nat} {k l : list A} {x : A} :
    m < n -> insert n x l = Some k ->
    nth_error k m = nth_error l m.
Proof.
  move: m l k.
  induction n;
  move=> m l k Hlt Hins.
  - destruct (Nat.nlt_0_r _ Hlt).
  - destruct l.
  --- discriminate Hins.
  --- simpl in Hins.
      destruct (insert n x l) as [j | ] eqn:Heq;
      simpl in Hins;
      try discriminate Hins.
      inversion Hins.
      destruct m.
  ----- auto.
  ----- simpl.
        rewrite <- Nat.succ_lt_mono in Hlt.
        apply IHn; auto.
Qed.

Lemma insert_nth_err_ge {A : Type} {m n : nat} {k l : list A} {x : A} :
    m >= n -> insert n x l = Some k ->
    nth_error k (S m) = nth_error l m.
Proof.
  move: m l k.
  induction n;
  move=> m l k Hge Hins.
  - simpl in Hins.
    inversion Hins.
    simpl.
    reflexivity.
  - destruct l;
    try discriminate Hins.
    simpl in Hins.
    destruct (insert n x l) as [j | ] eqn:Heq;
    try discriminate Hins.
    inversion Hins.
    simpl.
    destruct m;
    try destruct (Nat.nle_succ_0 _ Hge).
    simpl (nth_error (a :: l) (S m)).
    apply le_S_n in Hge.
    exact (IHn _ _ _ Hge Heq). 
Qed.

Lemma insert_nth_err {A : Type} {n : nat} {k l : list A} {x : A} :
    insert n x l = Some k -> nth_error k n = Some x.
Proof.
  move: k l.
  induction n;
  move => k l;
  intro Heq;
  simpl in Heq.
  - inversion Heq.
    auto.
  - destruct l;
    try discriminate Heq.
    destruct (insert n x l) eqn:Hins;
    try discriminate Heq; simpl in Heq.
    inversion Heq.
    simpl.
    eapply IHn.
    exact Hins.
Qed.

Definition binsert (n : nat) (t : typeT) (G : Context.t) :
    option (Context.t) :=
  option_map (fun l => {|
      Context.bmap := l;
      Context.fmap := Context.fmap G
    |}) (insert n t (Context.bmap G)).

Lemma binsert_bMapsTo {n : nat} {G H : Context.t} {t : typeT} :
    binsert n t G = Some H -> Context.bMapsTo n t H.
Proof.
  unfold binsert.
  intro Heq1.
  destruct (insert n t (Context.bmap G)) as [l | ] eqn:Heq2;
  try discriminate Heq1.
  simpl in Heq1.
  inversion Heq1.
  unfold Context.bMapsTo.
  simpl.
  eapply insert_nth_err.
  exact Heq2.
Qed.

Lemma binsert_bMapsTo_lt {m n : nat} {G H : Context.t} {t u : typeT} :
    m < n -> binsert n t G = Some H ->
    Context.bMapsTo m u G <-> Context.bMapsTo m u H.
Proof.
  unfold binsert.
  intros Hlt Heq1.
  destruct (insert n t (Context.bmap G)) as [l | ] eqn:Heq2;
  try discriminate Heq1.
  simpl in Heq1.
  inversion Heq1.
  unfold Context.bMapsTo.
  simpl.
  erewrite <- insert_nth_err_lt.
  - reflexivity.
  - exact Hlt.
  - exact Heq2.    
Qed.

Lemma binsert_bMapsTo_ge {m n : nat} {G H : Context.t} {t u : typeT} :
    m >= n -> binsert n t G = Some H ->
    Context.bMapsTo m u G <-> Context.bMapsTo (S m) u H.
Proof.
  unfold binsert.
  intros Hlt Heq1.
  destruct (insert n t (Context.bmap G)) as [l | ] eqn:Heq2;
  try discriminate Heq1.
  simpl in Heq1.
  inversion Heq1.
  unfold Context.bMapsTo.
  simpl Context.bmap.
  erewrite <- insert_nth_err_ge.
  - reflexivity.
  - exact Hlt.
  - exact Heq2.    
Qed.

Lemma binsert_0_bpush {t : typeT} {G : Context.t} :
    binsert O t G = Some (Context.bpush t G).
Proof.
  unfold binsert, Context.bpush.
  simpl.
  reflexivity.
Qed.

Lemma binsert_bpush {n : nat} {t u : typeT} {G H : Context.t} :
    binsert n t G = Some H ->
    binsert (S n) t (Context.bpush u G) = Some (Context.bpush u H).
Proof.
  unfold binsert.
  destruct G.
  simpl.
  intro Heq1.
  destruct (insert n t bmap) as [l | ] eqn:Heq2;
  try discriminate Heq1.
  simpl in Heq1.
  inversion Heq1.
  unfold Context.bpush.
  reflexivity.
Qed.

Lemma binsert_bshift {G H : Context.t} {e : termT} {t u : typeT} :
    G |- e :T t ->
    forall n : nat,
    binsert n u G = Some H ->
    H |- (bshift n e) :T t.
Proof.
  intro He.
  move: H.
  induction He;
  move=> I;
  intros m Hins;
  simpl;
  eauto using derivation.
  - destruct (m <=? n) eqn:Hcomp;
    unfold binsert in Hins;
    destruct (insert m u (Context.bmap G)) eqn:Heq;
    simpl in Hins;
    try discriminate Hins;
    apply bvarT_ax;
    unfold Context.bMapsTo in H;
    unfold Context.bMapsTo;
    destruct I;
    inversion Hins;
    simpl Context.bmap.
  --- apply Compare_dec.leb_complete in Hcomp.
      erewrite insert_nth_err_ge.
  ----- exact H. 
  ----- exact Hcomp.
  ----- rewrite H1 in Heq.
        exact Heq.
  --- apply Compare_dec.leb_complete_conv in Hcomp.
      erewrite insert_nth_err_lt.
  ----- exact H.
  ----- exact Hcomp.
  ----- rewrite H1 in Heq.
        exact Heq.  
  - apply fvarT_ax.
    destruct (insert m u (Context.bmap G)) eqn:Heq;
    unfold binsert in Hins;
    rewrite Heq in Hins;
    simpl in Hins;
    try discriminate Hins.
    destruct I.
    unfold Context.fMapsTo.
    simpl.
    inversion Hins.
    exact H.
  - apply absT_in.
    apply IHHe.
    exact (@binsert_bpush _ _ t _ _ Hins).
Qed.

Lemma bpush_bshift {G : Context.t} {e : termT} {t u : typeT} :
    G |- e :T t ->
    (Context.bpush u G) |- (bshift O e) :T t.
Proof.
  intro Hder.
  eapply binsert_bshift.
  - exact Hder.
  - rewrite binsert_0_bpush.
    reflexivity.
Qed.

Lemma binsert_fmap {n : nat} {G H : Context.t} {t : typeT} :
    binsert n t G = Some H -> Context.fmap G = Context.fmap H.
Proof.
  unfold binsert.
  intro Heq1.
  destruct (insert n t (Context.bmap G)) as [l | ] eqn:Heq2;
  try discriminate Heq1.
  simpl in Heq1.
  inversion Heq1.
  auto.
Qed.

Lemma binsert_fMapsTo {n : nat} {G H : Context.t} {t u : typeT} {x : fident} :
    binsert n t G = Some H ->
    Context.fMapsTo x u G <-> Context.fMapsTo x u H.
Proof.
  intro Heq.
  unfold Context.fMapsTo.
  rewrite (binsert_fmap Heq).
  reflexivity.
Qed.

Lemma derivation_bsubst
  {G H : Context.t} {n : nat} {e a : termT} {t u : typeT} :
    binsert n t G = Some H ->
    H |- e :T u ->
    G |- a :T t ->
    G |- e[n <- a] :T u.
Proof.
  move: G H n u a.
  induction e;
  move=> G H m u a Hins He Ha;
  inversion He;
  eauto using derivation;
  simpl.
  - apply fvarT_ax.
    rewrite (binsert_fMapsTo Hins). 
    exact H2.
  - destruct (m ?= n) eqn:Hcomp.
  --- apply Nat.compare_eq in Hcomp.
      rewrite Hcomp in Hins.
      apply binsert_bMapsTo in Hins.
      rewrite (Context.bMapsTo_fun H2 Hins).
      exact Ha.
  --- apply Compare_dec.nat_compare_Lt_lt in Hcomp.
      destruct n as [ | n];
      try destruct (Nat.nlt_0_r _ Hcomp).
      rewrite Nat.lt_succ_r in Hcomp.
      apply bvarT_ax.
      rewrite (binsert_bMapsTo_ge Hcomp Hins).
      exact H2.
  --- apply Compare_dec.nat_compare_Gt_gt in Hcomp.
      apply bvarT_ax.
      rewrite (binsert_bMapsTo_lt Hcomp Hins).
      exact H2.
  - apply absT_in.
    eapply IHe.
  --- exact (binsert_bpush Hins).
  --- exact H2.
  --- exact (bpush_bshift Ha).
Qed.

Lemma derivation_one_reduction {G : Context.t} {e f : termT} {t : typeT} :
    e ->1 f -> G |- e :T t -> G |- f :T t.
Proof.
  intro Hred.
  move: G t.
  induction Hred;
  move=> G t Hder;
  inversion Hder;
  eauto using derivation.
  - inversion H2.
    eapply derivation_bsubst;
    eauto using binsert_0_bpush.
  - inversion H6.
    eauto using derivation.
Qed.

Lemma derivation_reduction
  {G : Context.t} {e f : termT} {t : typeT} {n : nat} :
    (e ->(n) f) -> G |- e :T t -> G |- f :T t.
Proof.
  intros Hred.
  induction Hred;
  eauto using derivation_one_reduction.
Qed.

Lemma derivation_reduction_star
  {G : Context.t} {e f : termT} {t : typeT} :
    (e ->* f) -> G |- e :T t -> G |- f :T t.
Proof.
  intro Hred.
  destruct Hred as [n Hn].
  exact (derivation_reduction Hn).
Qed.
