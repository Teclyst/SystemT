(** * Terms

    In this file, System-T terms are defined, with a few base notions
    related to them (closedness, substitutions).
*)

Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import ident.

Require Import ssreflect ssrfun ssrbool.

Declare Scope system_t_term_scope.

(** ** Terms
*)

Declare Module FIdent : IDENT.

Module FIdentFacts := IdentFacts FIdent.

Infix "=?f" := FIdentFacts.eqb (at level 70).

(** [idenT] is the label type for free variables.
*)
Definition fident := FIdent.t.

(** [termT] is the [Type] representing the terms of System-T.

    Free variables are distinguished from bound variables, to avoid
    alpha-conversion issues.

    Free variables are labeled with [fident] values.

    Bound variables are represented by de Bruijn indexes. Because of
    that, a [termT] may correspond to something that is not a real
    System-T term, because some of its bound variables may be bound to
    nonexistant lambdas.
*)
Inductive termT :=
  | fvarT : fident -> termT
  | bvarT : nat -> termT
  | absT : termT -> termT
  | appT : termT -> termT -> termT
  | trueT : termT
  | falseT : termT
  | iteT : termT -> termT -> termT -> termT
  | oT : termT
  | sT : termT -> termT
  | recT : termT -> termT -> termT -> termT.

(** ** Closedness : Definitions
*)

(** A [termT] is [bound_nclosed n] when all its de Bruijn indexes
    refer to lambdas that are at height at most [n] above its root.

    Obviously, the good notion of closedness is [bound_nclosed O],
    as it states that all bound variables are bound to lambdas
    actually within the term, but we use a depth-dependent version
    as it is needed for the inductive structure. 
*)
Inductive bound_nclosed : nat -> termT -> Prop :=
  | fvarT_closed :
    forall n : nat, forall x : fident,
    bound_nclosed n (fvarT x)
  | bvarT_closed :
    forall n x : nat, x <= n ->
    bound_nclosed n (bvarT x)
  | absT_closed :
    forall n : nat, forall e : termT,
    bound_nclosed (S n) e ->
    bound_nclosed n (absT e)
  | appT_closed :
    forall n : nat, forall e f : termT,
    bound_nclosed n e ->
    bound_nclosed n f ->
    bound_nclosed n (appT e f)
  | trueT_closed :
    forall n : nat, bound_nclosed n trueT
  | falseT_closed :
    forall n : nat, bound_nclosed n falseT
  | iteT_closed :
    forall n : nat, forall e f g : termT,
    bound_nclosed n e ->
    bound_nclosed n f ->
    bound_nclosed n g ->
    bound_nclosed n (iteT e f g)
  | oT_closed :
    forall n : nat, bound_nclosed n oT
  | sT_closed :
    forall n : nat, forall e : termT,
    bound_nclosed n e ->
    bound_nclosed n (sT e)
  | recT_closed :
    forall n : nat, forall e f g : termT,
    bound_nclosed n e ->
    bound_nclosed n f ->
    bound_nclosed n g ->
    bound_nclosed n (recT e f g).

(** ** Closedness : Decidability
*)

(** A [termT] is [bound_closed] when all its bound variables are
    bound to lambdas actually within the term.
*)
Definition bound_closed := bound_nclosed O.

(** [bound_nclosed n] is a decidable predicate for all [n].
*)
Lemma bound_nclosed_decidable (e : termT) :
    forall n : nat, decidable (bound_nclosed n e).
Proof.
  induction e;
  intro m;
  [ |
    destruct (le_dec n m) |
    destruct (IHe (S m)) |
    destruct (IHe1 m); destruct (IHe2 m) | | |
    destruct (IHe1 m); destruct (IHe2 m); destruct (IHe3 m) | | 
    destruct (IHe m) |
    destruct (IHe1 m); destruct (IHe2 m); destruct (IHe3 m)
  ];
    try (left; auto using bound_nclosed; fail);
    right; intro Hn; inversion Hn; auto using bound_nclosed.
Qed.

(* * [bound_closed n] is a decidable predicate.
 *)
Lemma bound_closed_decidable (e : termT) :
    decidable (bound_closed e).
Proof.
  exact (bound_nclosed_decidable e O).
Qed.

(** ** Substitutions
*)

Fixpoint shift_bvarT (m n : nat) (e : termT) :=
  match e with
  | bvarT o =>
    match ltb n o with
    | true => bvarT (o + m)
    | _ => bvarT o
    end
  | absT e => absT (shift_bvarT m (S n) e)
  | appT e f =>
    appT (shift_bvarT m n e) (shift_bvarT m n f)
  | sT e => sT (shift_bvarT m n e)
  | iteT e f g =>
    iteT
      (shift_bvarT m n e)
      (shift_bvarT m n f)
      (shift_bvarT m n g)
  | recT e f g =>
    recT
      (shift_bvarT m n e)
      (shift_bvarT m n f)
      (shift_bvarT m n g)
  | _ => e
  end.

(** [subst_bvarT n e a] is [e], where all the occurrences of the
    variable bound by the lambda at height [n] above the root are
    replaced by [a].
*)
Fixpoint subst_bvarT (n : nat) (e a : termT) :=
  match e with
  | bvarT m => 
    match n =? m with
    | true => shift_bvarT n O a
    | false => bvarT m
    end
  | absT e => absT (subst_bvarT (S n) e a)
  | appT e f =>
    appT (subst_bvarT n e a) (subst_bvarT n f a)
  | sT e => sT (subst_bvarT n e a)
  | iteT e f g =>
    iteT
      (subst_bvarT n e a)
      (subst_bvarT n f a)
      (subst_bvarT n g a)
  | recT e f g =>
    recT
      (subst_bvarT n e a)
      (subst_bvarT n f a)
      (subst_bvarT n g a)
  | _ => e
  end.

Notation "e [ n <- f ]" := (subst_bvarT n e f) (at level 50).

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
    one_reduction (recT oT e f) e
  | redex_recT_sT :
    forall e f g : termT,
    one_reduction (recT (sT e) f g) (appT g (recT e f g))
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

Inductive reduction : nat -> termT -> termT -> Prop :=
  | red_refl_zero : forall e : termT, reduction O e e
  | red_next :
    forall n : nat, forall e f g : termT,
    one_reduction e f -> reduction n f g -> 
    reduction (S n) e g.

Notation "e ->( n ) f" := (reduction n e f) (at level 80).

Definition reduction_star (e f : termT) : Prop :=
    exists n : nat, e ->(n) f.

Notation "e ->* f" := (reduction_star e f) (at level 80).

Lemma one_reduction_reduction_1 {e f : termT} :
    one_reduction e f <-> (e ->(1) f).
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
    (e ->(n) f) -> one_reduction f g -> (e ->(S n) g).
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