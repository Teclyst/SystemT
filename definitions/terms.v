(** * Terms

    In this file, System-T terms are defined, with a few base notions
    related to them (closedness, substitutions).
*)

Require Import Nat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.

Declare Scope system_t_term_scope.

(** ** Terms
*)

(** [idenT] is the label type for free variables.
*)
Definition identT := nat.

(** [termT] is the [Type] representing the terms of System-T.

    Free variables are distinguished from bound variables, to avoid
    alpha-conversion issues.

    Free variables are labeled with [identT] values.

    Bound variables are represented by de Bruijn indexes. Because of
    that, a [termT] may correspond to something that is not a real
    System-T term, because some of its bound variables may be bound to
    nonexistant lambdas.
*)
Inductive termT :=
  | fvarT : identT -> termT
  | bvarT : nat -> termT
  | absT : termT -> termT
  | appT : termT -> termT -> termT
  | oT : termT
  | sT : termT -> termT
  | trueT : termT
  | falseT : termT
  | iteT : termT -> termT -> termT -> termT
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
    forall n : nat, forall x : identT,
    bound_nclosed n (fvarT x)
  | bvarT_closed :
    forall n x : nat, x <= n ->
    bound_nclosed n (bvarT x)
  | absT_closed :
    forall n : nat, forall u : termT,
    bound_nclosed (S n) u ->
    bound_nclosed n (absT u)
  | appT_closed :
    forall n : nat, forall u v : termT,
    bound_nclosed n u ->
    bound_nclosed n v ->
    bound_nclosed n (appT u v)
  | oT_closed :
    forall n : nat, bound_nclosed n oT
  | sT_closed :
    forall n : nat, forall u : termT,
    bound_nclosed n u ->
    bound_nclosed n (sT u)
  | trueT_closed :
    forall n : nat, bound_nclosed n trueT
  | falseT_closed :
    forall n : nat, bound_nclosed n falseT
  | iteT_closed :
    forall n : nat, forall u v w : termT,
    bound_nclosed n u ->
    bound_nclosed n v ->
    bound_nclosed n w ->
    bound_nclosed n (iteT u v w)
  | recT_closed :
    forall n : nat, forall u v w : termT,
    bound_nclosed n u ->
    bound_nclosed n v ->
    bound_nclosed n w ->
    bound_nclosed n (recT u v w).

(** ** Closedness : Decidability
*)

(** A [termT] is [bound_closed] when all its bound variables are
    bound to lambdas actually within the term.
*)
Definition bound_closed := bound_nclosed O.

(** [bound_nclosed n] is a decidable predicate for all [n].
*)
Lemma bound_nclosed_decidable (u : termT) :
    forall n : nat, decidable (bound_nclosed n u).
Proof.
  induction u;
  intro m;
  [ |
    destruct (dec_le n m) |
    destruct (IHu (S m)) |
    destruct (IHu1 m); destruct (IHu2 m) | |
    destruct (IHu m) | | |
    destruct (IHu1 m); destruct (IHu2 m); destruct (IHu3 m) |
    destruct (IHu1 m); destruct (IHu2 m); destruct (IHu3 m)
  ];
    try (left; auto using bound_nclosed; fail);
    right; intro Hn; inversion Hn; auto using bound_nclosed.
Qed.

(** [bound_closed n] is a decidable predicate.
*)
Lemma bound_closed_decidable (u : termT) :
    decidable (bound_closed u).
Proof.
  exact (bound_nclosed_decidable u O).
Qed.

(** ** Substitutions
*)

(** [subst_bvarT n u a] is [u], where all the occurrences of the
    variable bound by the lambda at height [n] above the root are
    replaced by [a].
*)
Fixpoint subst_bvarT (n : nat) (u a : termT) :=
  match u with
  | bvarT m => 
    match n =? m with
    | true => a
    | false => bvarT m
    end
  | absT u => absT (subst_bvarT (S n) u a)
  | appT u v =>
    appT (subst_bvarT n u a) (subst_bvarT n v a)
  | sT u => sT (subst_bvarT n u a)
  | iteT u v w =>
    iteT
      (subst_bvarT n u a)
      (subst_bvarT n v a)
      (subst_bvarT n w a)
  | recT u v w =>
    recT
      (subst_bvarT n u a)
      (subst_bvarT n v a)
      (subst_bvarT n w a)
  | _ => u
  end.

(** [subst_fvarT x u a] is [u], where all the occurrences of the
    free variable labeled by [x] are replaced by [a].
*)
Fixpoint subst_fvarT (x : identT) (u a : termT) :=
  match u with
  | fvarT y => 
    match x =? y with
    | true => a
    | false => bvarT y
    end
  | absT u => absT (subst_fvarT x u a)
  | appT u v =>
    appT (subst_fvarT x u a) (subst_fvarT x v a)
  | sT u => sT (subst_fvarT x u a)
  | iteT u v w =>
    iteT
      (subst_fvarT x u a)
      (subst_fvarT x v a)
      (subst_fvarT x w a)
  | recT u v w =>
    recT
      (subst_fvarT x u a)
      (subst_fvarT x v a)
      (subst_fvarT x w a)
  | _ => u
  end.