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
  simpl.
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
  - rewrite (IHe1 _ _ H4).
    rewrite (IHe2 _ _ H4).
    reflexivity.
  - rewrite (IHe1 _ _ H4).
    rewrite (IHe2 _ _ H4).
    rewrite (IHe3 _ _ H4).
    reflexivity.
  - rewrite (IHe _ _ H4).
    reflexivity.
  - rewrite (IHe1 _ _ H4).
    rewrite (IHe2 _ _ H4).
    rewrite (IHe3 _ _ H4).
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
  eauto.
  - simpl;
    destruct (PeanoNat.Nat.compare m' n') eqn:H1;
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
  - simpl.
    rewrite bshift_bshift.
    lia.
    f_equal.
    apply IHe.
    lia.
  - simpl.
    f_equal;
    eauto.
  - simpl.
    f_equal;
    eauto.
  - simpl.
    f_equal;
    eauto.
  - simpl.
    f_equal;
    eauto.
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

Definition FMap_union {elt elt' : Type} :=
  FMap.map2 (fun (_ : option elt) (_ : option elt') => Some tt).

Lemma FMap_unit_union_spec
  {elt elt' : Type} {s : FMap.t elt} {t : FMap.t elt'} {x : fident} :
    FMap.In x (FMap_union s t) <-> FMap.In x s \/ FMap.In x t.
Proof.
  constructor; unfold FMap_union.
  - exact (@FMap.map2_2 _ _ _ _ _ _ _).
  - intro Hor.
    unfold FMap.In.
    exists tt.
    apply FMap.find_2.
    apply FMap.map2_1.
    assumption.
Qed. 

Fixpoint free_fvarT (e : termT) : FMap.t unit :=
  match e with
  | fvarT x => FMap.add x tt (FMap.empty unit)
  | absT e
  | sT e => free_fvarT e
  | appT e f => FMap_union (free_fvarT e) (free_fvarT f)
  | iteT e f g
  | recT e f g =>
    FMap_union
      (free_fvarT e)
      (FMap_union (free_fvarT f) (free_fvarT g))
  | _ =>
    (FMap.empty unit)
  end.

Module NatMapFacts.
  Include FSets.FMapFacts.Facts NatMap.
  Include FSets.FMapFacts.Properties NatMap.
End NatMapFacts.

Lemma Tra_shifted {A : Type} : NatMapFacts.transpose_neqkey
  (@NatMap.Equal A)
  (fun (n : nat) => NatMap.add (S n)).
Proof.
  move=> m n e f s Hneq o.
  destruct (Nat.eqb (S m) o) eqn:Heq1;
  move/ PeanoNat.Nat.eqb_spec in Heq1;
  destruct (Nat.eqb (S n) o) eqn:Heq2;
  move/ PeanoNat.Nat.eqb_spec in Heq2.
  - destruct Hneq.
    lia.
  - rewrite (NatMapFacts.add_neq_o _ (x := S n) (y := o)).
    assumption.
    repeat rewrite NatMapFacts.add_eq_o;
    auto.
  - rewrite (NatMapFacts.add_neq_o _ (x := S m) (y := o)).
    assumption.
    repeat rewrite NatMapFacts.add_eq_o;
    auto.
  - repeat rewrite NatMapFacts.add_neq_o;
    auto.
Qed.

Lemma Proper_shifted {A : Type} : Morphisms.Proper (eq ==> eq ==> @NatMap.Equal A ==> @NatMap.Equal A)
  (fun n => NatMap.add (S n)).
Proof.
  move=> m n Heq1 e f Heq2 s t Heq3 o.
  rewrite Heq1.
  rewrite Heq2.
  destruct (Nat.eqb (S n) o) eqn:Heq4;
  move/ PeanoNat.Nat.eqb_spec in Heq4.
  - repeat rewrite NatMapFacts.add_eq_o;
    auto.
  - repeat rewrite NatMapFacts.add_neq_o;
    auto.
Qed.

Lemma shifted_NatMap_spec1 {A : Type} {s : NatMap.t A} {n : nat} {a : A} :
  NatMap.MapsTo n a s -> NatMap.MapsTo (S n) a (shifted_NatMap s).
Proof.
  unfold shifted_NatMap.
  move: s.
  apply (NatMapFacts.map_induction (P := fun s => NatMap.MapsTo n a s -> NatMap.MapsTo (S n) a (shifted_NatMap s))).
  - move=> s Hem Hmap.
    unfold NatMap.Empty.
    destruct (Hem _ _ Hmap).
  - move=> s t Hind m b Hnin Hadd Hmap.
    unfold shifted_NatMap.
    rewrite (NatMapFacts.fold_Add (eqA := NatMap.Equal) _ _ _ _ (m1 := s) _ (k := m) (e := b)).
  --- exact Proper_shifted.
  --- exact Tra_shifted.
  --- assumption.
  --- assumption.
  --- destruct (Nat.eqb m n) eqn:Heq;
      move/ PeanoNat.Nat.eqb_spec in Heq.
  ----- rewrite <- Heq.
        rewrite <- Heq in Hmap.
        have Heq2 := Hadd m.
        rewrite NatMapFacts.add_eq_o in Heq2.
        reflexivity.
        rewrite (NatMap.find_1 (e := a)) in Heq2.
        assumption.
        inversion Heq2.
        apply NatMap.add_1.
        reflexivity.
  ----- apply NatMap.add_2.
        lia.
        apply Hind.
        have Heq2 := Hadd n.
        rewrite (NatMap.find_1 (e := a)) in Heq2.
        assumption.
        rewrite NatMapFacts.add_neq_o in Heq2.
        assumption.
        apply NatMap.find_2.
        auto.
Qed.

Lemma shifted_NatMap_spec2 {A : Type} {s : NatMap.t A} {n : nat} {a : A} :
  NatMap.MapsTo n a (shifted_NatMap s) ->
  exists m : nat, n = S m /\ NatMap.MapsTo m a s.
Proof.
  move: s.
  apply (NatMapFacts.map_induction
    (P := fun s =>
      NatMap.MapsTo n a (shifted_NatMap s) ->
  exists m : nat, n = S m /\ NatMap.MapsTo m a s)).
  - move=> s Hem Hmap.
    unfold shifted_NatMap in Hmap.
    rewrite NatMapFacts.fold_Empty in Hmap.
    assumption.
    destruct (NatMap.empty_1 Hmap).
  - move=> s t Hind m b Hnin Hadd Hmap.
    unfold shifted_NatMap in Hmap.
    rewrite (NatMapFacts.fold_Add (eqA := NatMap.Equal) _ _ _ _ (m1 := s) _ (k := m) (e := b)) in Hmap.
  --- exact Proper_shifted.
  --- exact Tra_shifted.
  --- assumption.
  --- assumption.
  --- destruct (Nat.eqb n (S m)) eqn:Heq;
      move/ PeanoNat.Nat.eqb_spec in Heq.
  ----- exists m.
        constructor.
  ------- assumption.
  ------- rewrite <- Heq in Hmap.
          rewrite NatMapFacts.add_mapsto_iff in Hmap.
          destruct Hmap as [[_ Heq2] | [Habs _]].
  --------- rewrite Heq2 in Hadd.
            have Heq3 := Hadd m.
            rewrite NatMapFacts.add_eq_o in Heq3.
            reflexivity.
            apply NatMap.find_2.
            exact Heq3.
  --------- destruct (Habs (eq_refl n)). 
  ----- apply (NatMap.add_3 (x := S m) (e := a)) in Hmap.
  ------- destruct (Hind Hmap) as [o [Heq2 Hmap2]].
          exists o.
          constructor.
  --------- exact Heq2.
  --------- have Heq3 := Hadd o.
            rewrite NatMapFacts.add_neq_o in Heq3.
            lia.
            rewrite (NatMap.find_1 (m := s) (e := a)) in Heq3.
            assumption.
            apply NatMap.find_2.
            assumption.
  ------- lia.
Qed.

Lemma shifted_NatMap_spec_iff {A : Type} {s : NatMap.t A} {n : nat} {a : A} :
  NatMap.MapsTo n a (shifted_NatMap s) <->
  exists m : nat, n = S m /\ NatMap.MapsTo m a s.
Proof.
  constructor.
  - exact shifted_NatMap_spec2.
  - move=> [m [Heq Hmap]].
    rewrite Heq.
    apply shifted_NatMap_spec1.
    assumption. 
Qed.

Lemma par_bsubst_bsubst {e f : termT} {m : nat} {s : NatMap.t termT} :
  (forall n : nat, NatMap.In n s -> m <= n) -> (par_bsubst s e) [m <- par_bsubst s f] =
    (par_bsubst s (e [m <- f])).
Proof.
  Admitted.

Inductive bvarT_no_occur : nat -> termT -> Prop :=
  | bvarT_no_occur_fvarT :
    forall n : nat, forall f : fident,
    bvarT_no_occur n (fvarT f) 
  | bvarT_no_occur_bvarT :
    forall n m : nat, m <> n -> bvarT_no_occur n (bvarT m)
  | bvarT_no_occur_absT :
    forall n : nat, forall e : termT, bvarT_no_occur (S n) e ->
    bvarT_no_occur n (absT e)
  | bvarT_no_occur_appT :
    forall n : nat, forall e f : termT,
    bvarT_no_occur n e -> bvarT_no_occur n f ->
    bvarT_no_occur n (appT e f)
  | bvarT_no_occur_falseT :
    forall n : nat, bvarT_no_occur n falseT
  | bvarT_no_occur_trueT :
    forall n : nat, bvarT_no_occur n trueT
  | bvarT_no_occur_iteT :
    forall n : nat, forall e f g : termT,
    bvarT_no_occur n e -> bvarT_no_occur n f -> bvarT_no_occur n g ->
    bvarT_no_occur n (iteT e f g)
  | bvarT_no_occur_oT :
    forall n : nat, bvarT_no_occur n oT
  | bvarT_no_occur_sT :
    forall n : nat, forall e : termT, bvarT_no_occur n e ->
    bvarT_no_occur n (sT e)
  | bvarT_no_occur_recT :
    forall n : nat, forall e f g : termT,
    bvarT_no_occur n e -> bvarT_no_occur n f -> bvarT_no_occur n g ->
    bvarT_no_occur n (recT e f g).

Lemma par_fsubst_subst {e f : termT} {m : nat} {s : FMap.t termT} :
  (par_fsubst (FMap.map (bshift m) s) e) [m <- par_fsubst s f] = (par_fsubst s (e [m <- f])).
Proof.
  move: f m.
  induction e;
  simpl.
  - move=> g m.
    destruct (FMap.find f s) eqn:Heq.
Admitted.

Lemma shifted_NatMap_empty {s : NatMap.t termT} :
  NatMap.Empty s -> NatMap.Empty (shifted_NatMap s).
Proof.
  move=> Hem.
  unfold shifted_NatMap.
  rewrite NatMapFacts.fold_Empty.
  - assumption.
  - exact (@NatMap.empty_1 termT).
Qed.

Lemma map_empty {A B : Type} {s : NatMap.t A} {f : A -> B} :
  NatMap.Empty s -> NatMap.Empty (NatMap.map f s).
Proof.
  move=> Hem n g Hmap.
  simpl in Hmap.
  have baz := NatMapFacts.map_mapsto_iff.
  unfold NatMap.MapsTo in baz.
  rewrite baz in Hmap.
  destruct Hmap as [a [_ Habs]].
  eapply (Hem n).
  exact Habs.
Qed.

Lemma par_bsubst_empty {e : termT} {s : NatMap.t termT} :
  NatMap.Empty s -> par_bsubst s e = e.
Proof.
  move: s.
  induction e;
  move=> s Hem;
  simpl;
  try f_equal;
  auto.
  - destruct (NatMap.find n s) eqn:Heq.
  --- apply NatMap.find_2 in Heq.
      destruct (Hem n t Heq).
  --- reflexivity.
  - f_equal.
    apply IHe.
    apply map_empty.
    apply shifted_NatMap_empty.
    assumption.
Qed.
