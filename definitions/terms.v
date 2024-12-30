(** * Terms

    In this file, System-T terms are defined, with a few base notions
    related to them (closedness, substitutions).
*)

Require Import Nat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import ident.

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
    destruct (dec_le n m) |
    destruct (IHe (S m)) |
    destruct (IHe1 m); destruct (IHe2 m) | |
    destruct (IHe m) | | |
    destruct (IHe1 m); destruct (IHe2 m); destruct (IHe3 m) |
    destruct (IHe1 m); destruct (IHe2 m); destruct (IHe3 m)
  ];
    try (left; auto using bound_nclosed; fail);
    right; intro Hn; inversion Hn; auto using bound_nclosed.
Qed.

(** [bound_closed n] is a decidable predicate.
*)
Lemma bound_closed_decidable (e : termT) :
    decidable (bound_closed e).
Proof.
  exact (bound_nclosed_decidable e O).
Qed.

(** ** Substitutions
*)

(** [subst_bvarT n e a] is [e], where all the occurrences of the
    variable bound by the lambda at height [n] above the root are
    replaced by [a].
*)
Fixpoint subst_bvarT (n : nat) (e a : termT) :=
  match e with
  | bvarT m => 
    match n =? m with
    | true => a
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

(** [subst_fvarT x e a] is [e], where all the occurrences of the
    free variable labeled by [x] are replaced by [a].
*)
Fixpoint subst_fvarT (x : fident) (e a : termT) :=
  match e with
  | fvarT y => 
    match x =?f y with
    | true => a
    | false => fvarT y
    end
  | absT e => absT (subst_fvarT x e a)
  | appT e f =>
    appT (subst_fvarT x e a) (subst_fvarT x f a)
  | sT e => sT (subst_fvarT x e a)
  | iteT e f g =>
    iteT
      (subst_fvarT x e a)
      (subst_fvarT x f a)
      (subst_fvarT x g a)
  | recT e f g =>
    recT
      (subst_fvarT x e a)
      (subst_fvarT x f a)
      (subst_fvarT x g a)
  | _ => e
  end.