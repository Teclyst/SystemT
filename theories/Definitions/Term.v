(** * Term

    In this file, System-T terms are defined, with a few base notions
    related to them (closedness, substitutions).
*)

Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import Definitions.Ident.

Require Import ssreflect ssrfun ssrbool.

Declare Scope system_t_term_scope.
Open Scope system_t_term_scope.

(** ** Terms
*)

Module FIdent <: IDENT := StringIdent.

Module FIdentFacts := IdentFacts FIdent.

(** [termT] is the [Type] representing the terms of System-T.

    Free variables are distinguished from bound variables, to avoid
    alpha-conversion issues.

    Free variables are labeled with [FIdent.t] values.

    Bound variables are represented by de Bruijn indexes. Because of
    that, a [termT] may correspond to something that is not a real
    System-T term, because some of its bound variables may be bound to
    nonexistant lambdas.
*)
Inductive termT :=
  | fvarT : FIdent.t -> termT
  | bvarT : nat -> termT
  | absT : termT -> termT
  | appT : termT -> termT -> termT
  | pairT : termT -> termT -> termT
  | plT : termT -> termT
  | prT : termT -> termT
  | trueT : termT
  | falseT : termT
  | iteT : termT -> termT -> termT -> termT
  | oT : termT
  | sT : termT -> termT
  | recT : termT -> termT -> termT -> termT.

Definition bool_as_boolT (b : bool) : termT :=
  match b with
  | true => trueT
  | _ => falseT
  end.

Fixpoint nat_as_natT (n : nat) : termT :=
  match n with
  | O => oT
  | S n => sT (nat_as_natT n)
  end.

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
    forall n : nat, forall x : FIdent.t,
    bound_nclosed n (fvarT x)
  | bvarT_closed :
    forall n x : nat, x < n ->
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
  | pairT_closed :
    forall n : nat, forall e f : termT,
    bound_nclosed n e ->
    bound_nclosed n f ->
    bound_nclosed n (pairT e f)
  | plT_closed :
    forall n : nat, forall e : termT,
    bound_nclosed n e ->
    bound_nclosed n (plT e)
  | prT_closed :
    forall n : nat, forall e : termT,
    bound_nclosed n e ->
    bound_nclosed n (prT e)
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
  intro m; [
    |
    destruct (lt_dec n m) |
    destruct (IHe (S m)) |
    destruct (IHe1 m); destruct (IHe2 m) |
    destruct (IHe1 m); destruct (IHe2 m) |
    destruct (IHe m) |
    destruct (IHe m) | | |
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

Fixpoint bshift (n : nat) (e : termT) :=
  match e with
  | bvarT m =>
    match leb n m with
    | true => bvarT (S m)
    | _ => bvarT m
    end
  | absT e => absT (bshift (S n) e)
  | appT e f =>
    appT (bshift n e) (bshift n f)
  | pairT e f =>
    pairT (bshift n e) (bshift n f)
  | plT e => plT (bshift n e)
  | prT e => prT (bshift n e)
  | sT e => sT (bshift n e)
  | iteT e f g =>
    iteT
      (bshift n e)
      (bshift n f)
      (bshift n g)
  | recT e f g =>
    recT
      (bshift n e)
      (bshift n f)
      (bshift n g)
  | _ => e
  end.

(** [bsubst n e a] is [e], where all the occurrences of the
    variable bound by the lambda at height [n] above the root are
    replaced by [a].

    Some modifications of de Bruijn indexes also occur: some
    indexes are shifted up, as if the lambda at height [n] had
    been eliminated, to behave correctly with regards to
    beta-reduction.
*)
Fixpoint bsubst (n : nat) (e a : termT) :=
  match e with
  | bvarT m => 
    match n ?= m with
    | Eq => a
    | Gt => bvarT m
    | Lt =>
      match m with
      | S m => bvarT m
      | O => bvarT O (* This case cannot happen in practice. *)
      end
    end
  | absT e => absT (bsubst (S n) e (bshift O a))
  | appT e f =>
    appT (bsubst n e a) (bsubst n f a)
  | pairT e f =>
    pairT (bsubst n e a) (bsubst n f a)
  | plT e => plT (bsubst n e a)
  | prT e => prT (bsubst n e a)
  | sT e => sT (bsubst n e a)
  | iteT e f g =>
    iteT
      (bsubst n e a)
      (bsubst n f a)
      (bsubst n g a)
  | recT e f g =>
    recT
      (bsubst n e a)
      (bsubst n f a)
      (bsubst n g a)
  | _ => e
  end.

Fixpoint par_bsubst (n : nat) (s : list termT) (e : termT) :=
  match e with
  | bvarT m =>
    match (m <? n), (List.nth_error s (m - n)) with
    | true, _ => bvarT m
    | _, Some a => a
    | _, _ => bvarT (m - List.length s) 
    end
  | absT e => absT (par_bsubst (S n)
    (List.map (bshift O) s) e)
  | appT e f =>
    appT (par_bsubst n s e) (par_bsubst n s f)
  | pairT e f =>
    pairT (par_bsubst n s e) (par_bsubst n s f)
  | plT e => plT (par_bsubst n s e)
  | prT e => prT (par_bsubst n s e)
  | sT e => sT (par_bsubst n s e)
  | iteT e f g =>
    iteT
      (par_bsubst n s e)
      (par_bsubst n s f)
      (par_bsubst n s g)
    | recT e f g =>
      recT
        (par_bsubst n s e)
        (par_bsubst n s f)
        (par_bsubst n s g)
    | _ => e
  end.

Notation "e [ n <- f ]" := (bsubst n e f) (at level 50) : system_t_term_scope.

Module FMap := FIdent.Map.

Module FMapFacts := Coq.FSets.FMapFacts.WFacts FMap.

(** [fsubst x e a] is [e], where all the occurrences of the
    variable bound by the lambda at height [n] above the root are
    replaced by [a].
*)
Fixpoint fsubst (x : FIdent.t) (e a : termT) :=
  match e with
  | fvarT y =>
    match FIdentFacts.eqb x y with
    | true => a
    | _ => fvarT y
    end
  | absT e => absT (fsubst x e (bshift O a))
  | appT e f =>
    appT (fsubst x e a) (fsubst x f a)
  | pairT e f =>
    pairT (fsubst x e a) (fsubst x f a)
  | plT e => plT (fsubst x e a)
  | prT e => prT (fsubst x e a)
  | sT e => sT (fsubst x e a)
  | iteT e f g =>
    iteT
      (fsubst x e a)
      (fsubst x f a)
      (fsubst x g a)
  | recT e f g =>
    recT
      (fsubst x e a)
      (fsubst x f a)
      (fsubst x g a)
  | _ => e
  end.

Fixpoint par_fsubst (s : FMap.t termT) (e : termT) :=
  match e with
  | fvarT x => 
    match FMap.find x s with
    | Some a => a
    | _ => fvarT x
    end
  | absT e => absT (par_fsubst (FMap.map (bshift O) s) e)
  | appT e f =>
    appT (par_fsubst s e) (par_fsubst s f)
  | pairT e f =>
    pairT (par_fsubst s e) (par_fsubst s f)
  | plT e => plT (par_fsubst s e)
  | prT e => prT (par_fsubst s e)
  | sT e => sT (par_fsubst s e)
  | iteT e f g =>
    iteT
      (par_fsubst s e)
      (par_fsubst s f)
      (par_fsubst s g)
  | recT e f g =>
    recT
      (par_fsubst s e)
      (par_fsubst s f)
      (par_fsubst s g)
  | _ => e
  end.
