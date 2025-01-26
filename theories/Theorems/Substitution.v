Require Import Definitions.Ident.
Require Import Definitions.Term.
Require Import Lia.
Require Import Morphisms.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.

Lemma bound_closed_nat_as_natT {n : nat} :
    bound_closed (nat_as_natT n).
Proof.
  induction n;
  unfold bound_closed;
  simpl;
  auto using bound_nclosed.
Qed.

Lemma bound_closed_bool_as_boolT {b : bool} :
    bound_closed (bool_as_boolT b).
Proof.
  destruct b;
  unfold bound_closed;
  simpl;
  auto using bound_nclosed.
Qed.

Lemma bound_nclosed_le {m n : nat} {e : termT} :
    m <= n -> bound_nclosed m e -> bound_nclosed n e.
Proof.
  move=> Hle Hbndm.
  move: Hle.
  move: n.
  induction Hbndm;
  move=> o Hle;
  auto using bound_nclosed.
  - apply bvarT_closed.
    lia.
  - apply absT_closed.
    apply IHHbndm.
    lia.
Qed.

Lemma bound_closed_bound_nclosed {n : nat} {e : termT} :
    bound_closed e -> bound_nclosed n e.
Proof.
  unfold bound_closed.
  apply bound_nclosed_le.
  lia.
Qed.  

Lemma bshift_bshift {e : termT} {m n : nat} :
    m <= n -> bshift m (bshift n e) = bshift (S n) (bshift m e).
Proof.
  move: m n.
  induction e;
  move=> m' n' H4;
  eauto;
  simpl;
  try (
    try rewrite (IHe _ _ H4);
    try rewrite (IHe1 _ _ H4);
    try rewrite (IHe2 _ _ H4);
    try rewrite (IHe3 _ _ H4);
    reflexivity;
    fail
  ).
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
Qed.

Lemma bshift_bsubst_eq {e f : termT} {n : nat} :
    (bshift n e)[n <- f] = e.
Proof.
  move: f n.
  induction e;
  move=> g m;
  eauto;
  simpl;
  try (f_equal;
    auto).
  destruct (PeanoNat.Nat.leb m n) eqn:H1;
  move/ PeanoNat.Nat.leb_spec0 in H1;
  simpl.
  - destruct (PeanoNat.Nat.compare m (S n)) eqn:H2.
  --- rewrite PeanoNat.Nat.compare_eq_iff in H2.
        lia.
  --- rewrite PeanoNat.Nat.compare_lt_iff in H2.
        reflexivity.
  --- try rewrite PeanoNat.Nat.compare_gt_iff in H2.
        lia.
  - destruct (PeanoNat.Nat.compare m n) eqn:H2.
  --- rewrite PeanoNat.Nat.compare_eq_iff in H2.
        lia.
  --- rewrite PeanoNat.Nat.compare_lt_iff in H2.
        lia.
  --- try rewrite PeanoNat.Nat.compare_gt_iff in H2.
        reflexivity.
Qed.

Lemma bshift_bsubst {e f : termT} {m n : nat} :
    m <= n -> bshift n (e[m <- f]) = (bshift (S n) e)[m <- bshift n f].
Proof.
  move: f m n.
  induction e;
  move=> f' m' n' H4;
  eauto;
  simpl;
  try (
    f_equal;
    eauto
  ).
  - destruct (PeanoNat.Nat.compare m' n') eqn:H1;
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
  - rewrite bshift_bshift.
    lia.
    f_equal.
    apply IHe.
    lia.
Qed.

Lemma bshift_bsubst' {e f : termT} {m n : nat} :
    m <= n -> bshift m (e[n <- f]) = (bshift m e) [S n <- bshift m f].
Proof.
  move: f m n.
  induction e;
  move=> f' m' n' Hle;
  eauto; simpl;
  try (f_equal;
    auto).
  - destruct (PeanoNat.Nat.compare m' n) eqn:H1;
    destruct (PeanoNat.Nat.compare n' n) eqn:H2;
    try rewrite PeanoNat.Nat.compare_eq_iff in H1;
    try rewrite PeanoNat.Nat.compare_eq_iff in H2;
    try rewrite PeanoNat.Nat.compare_lt_iff in H1;
    try rewrite PeanoNat.Nat.compare_lt_iff in H2;
    try rewrite PeanoNat.Nat.compare_gt_iff in H1;
    try rewrite PeanoNat.Nat.compare_gt_iff in H2;
    try lia.
  --- move/ PeanoNat.Nat.leb_spec0 in Hle.
      rewrite H2 in Hle.
      rewrite Hle.
      simpl.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2;
      auto.
  --- rewrite H1.
      rewrite PeanoNat.Nat.leb_refl.
      simpl.  
      rewrite PeanoNat.Nat.leb_refl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2;
      auto.
  --- rewrite Compare_dec.leb_correct.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2;
      auto.
  --- destruct n.
  ----- lia.
  ----- simpl.
        rewrite Compare_dec.leb_correct.
        lia.
        rewrite Compare_dec.leb_correct.
        lia.
        simpl.
        rewrite (PeanoNat.Nat.compare_lt_iff _ _).2;
        auto.
  --- simpl.
      rewrite Compare_dec.leb_correct.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2;
      auto.
  --- simpl.
      rewrite Compare_dec.leb_correct_conv.
      lia.
      simpl.
      destruct n.
  ----- reflexivity.
  ----- rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
        lia.
        reflexivity.
  - f_equal.
    rewrite bshift_bshift.
    lia.
    apply IHe.
    lia.
Qed.

Lemma bsubst_bsubst {e f g : termT} {m n : nat} :
    m <= n -> e[m <- f][n <- g] = e[S n <- bshift m g][m <- f[n <- g]].
Proof.
  move: m n f g.
  induction e;
  move=> m' n' f' g' Hle;
  eauto;
  [ | | simpl; f_equal; auto ..].
  - destruct (PeanoNat.Nat.compare m' n) eqn:H1;
    destruct (PeanoNat.Nat.compare (S n') n) eqn:H2;
    try rewrite PeanoNat.Nat.compare_eq_iff in H1;
    try rewrite PeanoNat.Nat.compare_eq_iff in H2;
    try rewrite PeanoNat.Nat.compare_lt_iff in H1;
    try rewrite PeanoNat.Nat.compare_lt_iff in H2;
    try rewrite PeanoNat.Nat.compare_gt_iff in H1;
    try rewrite PeanoNat.Nat.compare_gt_iff in H2;
    destruct n;
    try lia;
    simpl.
  --- rewrite (PeanoNat.Nat.compare_eq_iff _ _).2.
      assumption.
      reflexivity.
  --- rewrite (PeanoNat.Nat.compare_gt_iff n' _).2.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2;
      auto.
  --- rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      assumption.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_eq_iff _ _).2.
      lia.
      simpl.
      rewrite bshift_bsubst_eq.
      reflexivity.
  --- rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      assumption.
      simpl.
      rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      lia.
      destruct n;
      simpl.
  ------ lia.
  ------ rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
         lia.
         reflexivity.
  --- rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      assumption.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_lt_iff _ _).2.
      assumption.
      reflexivity.
  --- rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      assumption.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      lia.
      reflexivity.
  --- rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      assumption.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      lia.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      lia.
      simpl.
      rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
      assumption.
      reflexivity.
  - simpl.
    f_equal.
    rewrite bshift_bshift.
    lia.
    rewrite (@bshift_bsubst');
    try apply IHe;
    lia.
Qed.

Lemma bound_nclosed_bshift {e : termT} {m n : nat} :
    m <= n -> bound_nclosed m e -> bshift n e = e.
Proof.
  move=> Hle Hbnd.
  move: n Hle.
  induction Hbnd;
  simpl;
  auto;
  move=> m Hle;
  try (
    f_equal; 
    auto
  ).
  - rewrite Compare_dec.leb_correct_conv.
    lia.
    reflexivity.
  - rewrite IHHbnd.
    lia.
    reflexivity.
Qed.

Lemma bound_nclosed_bsubst {e f : termT} {m n : nat} :
    m <= n -> bound_nclosed m e -> bsubst n e f = e.
Proof.
  move=> Hle Hbnd.
  move: f n Hle.
  induction Hbnd;
  simpl;
  auto;
  move=> h m Hle;
  try (
    f_equal; 
    auto
  ).
  - rewrite (PeanoNat.Nat.compare_gt_iff _ _).2.
    lia.
    reflexivity.
  - apply IHHbnd.
    lia. 
Qed.

Lemma bound_closed_bshift {e : termT} {n : nat} :
    bound_closed e -> bshift n e = e.
Proof.
  apply bound_nclosed_bshift.
  lia.
Qed.

Lemma bound_closed_bsubst {e f : termT} {n : nat} :
    bound_closed e -> bsubst n e f = e.
Proof.
  apply bound_nclosed_bsubst.
  lia.
Qed.

#[export] Instance Proper_par_fsusbst : Morphisms.Proper (@FMap.Equal termT ==> eq ==> eq)
  par_fsubst.
Proof.
  move=> s t Heq1 e f Heq2.
  rewrite <- Heq2.
  clear Heq2 f.
  move: s t Heq1.
  induction e;
  move=> s t Heq;
  simpl;
  try f_equal;
  eauto.
  - rewrite Heq.
    reflexivity.
  - apply IHe.
    move=> x.
    repeat rewrite FMapFacts.map_o.
    rewrite Heq.
    reflexivity.  
Qed.

Lemma FMap_map_map
  {A B C : Type} {f : A -> B} {g : B -> C} {s : FMap.t A} :
  FMap.Equal (FMap.map g (FMap.map f s)) (FMap.map (fun a => g (f a)) s).
Proof.
  move=> a.
  repeat rewrite FMapFacts.map_o.
  destruct (FMap.find a s);
  reflexivity.
Qed.

Lemma FMap_map_bshift_bshift
  {m n : nat} {s : FMap.t termT} :
    m <= n ->
      FMap.Equal
        (FMap.map (bshift m) (FMap.map (bshift n) s))
        (FMap.map (bshift (S n)) (FMap.map (bshift m) s)).
Proof.
  repeat rewrite FMap_map_map.
  move=> Hle a.
  repeat rewrite FMapFacts.map_o.
  destruct (FMap.find a s);
  simpl.
  - rewrite bshift_bshift.
    assumption.
    reflexivity. 
  - reflexivity.
Qed.

Lemma par_fsubst_bshift {e : termT} {m : nat} {s : FMap.t termT} :
  bshift m (par_fsubst s e) = par_fsubst (FMap.map (bshift m) s) (bshift m e).
Proof.
  move: m s.
  induction e;
  move=> m s;
  simpl;
  try f_equal;
  eauto.
  - rewrite FMapFacts.map_o.
    destruct (FMap.find k s);
    reflexivity.
  - destruct (PeanoNat.Nat.leb m n);
    reflexivity.
  - rewrite FMap_map_bshift_bshift.
    lia.
    exact (IHe _ _).
Qed.

Lemma par_fsubst_bsubst {e f : termT} {m : nat} {s : FMap.t termT} :
  (par_fsubst (FMap.map (bshift m) s) e) [m <- par_fsubst s f] = (par_fsubst s (e [m <- f])).
Proof.
  move: f m s.
  induction e;
  simpl;
  move=> g m s;
  try (
    f_equal;
    auto;
    fail
  ).
  - destruct (FMap.find k s) eqn:Heq.
  --- rewrite (FMap.find_1 (FMap.map_1 (bshift m) (FMap.find_2 Heq))).
      exact bshift_bsubst_eq.
  --- have foo : FMap.find k (FMap.map (bshift m) s) = None.
      rewrite FMapFacts.map_o.
      rewrite Heq.
      reflexivity.
      rewrite foo.
      reflexivity.
  - destruct (PeanoNat.Nat.compare m n);
    destruct n;
    reflexivity.
  - f_equal.
    simpl.
    rewrite FMap_map_bshift_bshift.
    lia.
    rewrite par_fsubst_bshift.
    exact (IHe _ _ _).
Qed.

Lemma par_bsubst_empty {e : termT} {n : nat} :
    par_bsubst n nil e = e.
Proof.
  move: n.
  induction e;
  move=> m;
  simpl;
  try f_equal;
  auto.
  - destruct (PeanoNat.Nat.ltb n m).
  --- reflexivity.
  --- destruct (n - m);
      destruct n;
      reflexivity. 
Qed.

Lemma par_bsubst_bsubst_eq {e f : termT} {n : nat} {s : list termT} :
    (par_bsubst (S n) (List.map (bshift n) s) e)[n <- f] =
    (par_bsubst n (f :: s) e).
Proof.
  move: n s f.
  induction e;
  move=> m s h;
  simpl;
  try (f_equal;
    auto).
  - destruct (PeanoNat.Nat.ltb n (S m)) eqn:Hlt1;
    destruct (PeanoNat.Nat.ltb n m) eqn:Hlt2;
    move/ PeanoNat.Nat.ltb_spec0 in Hlt1;
    move/ PeanoNat.Nat.ltb_spec0 in Hlt2;
    try lia;
    simpl;
    destruct (PeanoNat.Nat.compare m n) eqn:Hcomp;
    try rewrite PeanoNat.Nat.compare_eq_iff in Hcomp;
    try rewrite PeanoNat.Nat.compare_lt_iff in Hcomp;
    try rewrite PeanoNat.Nat.compare_gt_iff in Hcomp;
    try lia.
  --- reflexivity.
  --- rewrite Hcomp.
      rewrite PeanoNat.Nat.sub_diag.
      reflexivity.
  --- have Heq : (n - m = S (n - S m)).
      lia.
      rewrite Heq.
      simpl.
      rewrite List.nth_error_map.
      destruct (List.nth_error s (n - S m)) eqn:Heq2;
      simpl.
  ----- rewrite bshift_bsubst_eq.
        reflexivity.
  ----- rewrite List.map_length.
        rewrite List.nth_error_None in Heq2.
        destruct (PeanoNat.Nat.compare m (n - length s)) eqn:Hcomp2;
        try rewrite PeanoNat.Nat.compare_eq_iff in Hcomp2;
        try rewrite PeanoNat.Nat.compare_lt_iff in Hcomp2;
        try rewrite PeanoNat.Nat.compare_gt_iff in Hcomp2;
        destruct (n - length s) eqn:Heq3;
        try lia.
        have Heq4 : n - S (length s) = n0.
        lia.
        rewrite Heq4.
        reflexivity.
  - rewrite List.map_map.
    rewrite (List.map_ext _
      (fun x => bshift (S m) (bshift O x))).
  --- move=> f.
      apply bshift_bshift.
      lia.
  --- rewrite <- List.map_map.
      exact (IHe _ _ _). 
Qed.
