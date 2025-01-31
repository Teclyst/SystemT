Require Import Nat.
Require Import List.
Require Import Definitions.Ident.

Require Import ssreflect ssrfun ssrbool.

Declare Scope system_t_type_scope.
Open Scope system_t_type_scope.

Module TIdent <: IDENT := StringIdent.

Module TSet := StringSet.

Module TSetFacts.

  Include FSets.FSetFacts.Facts TSet.

  Include FSets.FSetProperties.Properties TSet.

  Include FSets.FSetDecide.Decide TSet.

End TSetFacts.

Module TMap := StringMap.

Module TMapFacts := FSets.FMapFacts.Facts TMap.

Module TIdentFacts := IdentFacts TIdent TSet TMap.

Inductive typeT :=
  | natT : typeT
  | boolT : typeT
  | tvarT : TIdent.t -> typeT
  | funT : typeT -> typeT -> typeT
  | prodT : typeT -> typeT -> typeT.

Notation "t ->T u" := (funT t u) (at level 35, right associativity) : system_t_type_scope.

Notation "t *T u" := (prodT t u) (at level 34, left associativity) : system_t_type_scope.

Fixpoint typeT_eqb (t u : typeT) :=
  match t, u with
  | tvarT x, tvarT y =>
    TIdentFacts.eqb x y
  | boolT, boolT
  | natT, natT =>
    true
  | t ->T u, v ->T w
  | t *T u, v *T w =>
    typeT_eqb t v && typeT_eqb v w
  | _, _  =>
    false
  end.

Fixpoint tsubst (x : TIdent.t) (a t : typeT) :=
  match t with
  | tvarT y =>
    match TIdentFacts.eqb x y with
    | true => a
    | _ => tvarT y
    end
  | funT t u =>
    funT (tsubst x a t) (tsubst x a u)
  | prodT t u =>
    prodT (tsubst x a t) (tsubst x a u)
  | _ =>
    t
  end.

Fixpoint par_tsubst (s : TMap.t typeT) (t : typeT) :=
  match t with
  | tvarT x =>
    match TMap.find x s with
    | Some a => a
    | _ => tvarT x
    end
  | funT t u =>
    funT (par_tsubst s t) (par_tsubst s u)
  | prodT t u =>
    prodT (par_tsubst s t) (par_tsubst s u)
  | _ =>
    t
  end.

Definition tsubst_compose (s h : TMap.t typeT) : TMap.t typeT :=
  TMap.map2
    (fun opt1 opt2 =>
      match opt1, opt2 with
      | Some t, _ => Some (par_tsubst h t)
      | _, Some t => Some t
      | _, _ => None end)
    s h.

Definition tsubst_add_l (x : TIdent.t) (t : typeT) (s : TMap.t typeT) :
    TMap.t typeT :=
  match TMap.find x s with
  | None => TMap.add x t (TMap.map (tsubst x t) s)
  | _ => TMap.map (tsubst x t) s
  end.

Definition tsubst_add_r (x : TIdent.t) (t : typeT) (s : TMap.t typeT) :
    TMap.t typeT :=
  TMap.add x (par_tsubst s t) s.

Definition ext_equal (r s : TMap.t typeT) : Prop :=
  forall t : typeT, par_tsubst r t = par_tsubst s t. 

Notation "r =ex s" := (ext_equal r s) (at level 50) : system_t_type_scope.

Definition tsubst_order_with_tsubst (q r s : TMap.t typeT) : Prop :=
  s =ex tsubst_compose r q.

Notation "r <|s( q ) s" := (tsubst_order_with_tsubst q r s) (at level 50).

Definition tsubst_order (r s : TMap.t typeT) : Prop :=
  exists q : TMap.t typeT, r <|s( q) s.

Notation "r <|s s" := (tsubst_order r s) (at level 50).

Definition unification_problem : Type := list (typeT * typeT).

Fixpoint variable_set (t : typeT) :=
  match t with
  | tvarT x => TSet.singleton x
  | t ->T u
  | t *T u =>
    TSet.union (variable_set t) (variable_set u)
  | _ =>
    TSet.empty
  end.

Fixpoint occurs (x : TIdent.t) (t : typeT) : bool :=
  match t with
  | tvarT y => TIdentFacts.eqb x y
  | t ->T u 
  | t *T u => occurs x t || occurs x u
  | _ => false
  end.

Fixpoint size (t : typeT) : nat :=
  match t with
  | t ->T u 
  | t *T u => S (size t + size u)
  | _ => S O
  end.

Lemma size_gt_O {t : typeT} : size t > O.
Proof.
  induction t;
  simpl;
  Lia.lia.
Qed.

Fixpoint problem_size (p : unification_problem) : nat :=
  match p with
  | nil => O
  | ((t, u) :: p)%list => size t + size u + problem_size p
  end.

Fixpoint problem_variable_set (p : unification_problem) : TSet.t :=
  match p with
  | nil => TSet.empty
  | ((t, u) :: p)%list =>
    TSet.union
      (TSet.union (variable_set t) (variable_set u))
      (problem_variable_set p)
  end.

Inductive unification_problem_order (p q : unification_problem) : Prop :=
  | card_lt :
    TSet.cardinal (problem_variable_set p) <
    TSet.cardinal (problem_variable_set q) ->
    unification_problem_order p q
  | card_le_size_lt :
    TSet.cardinal (problem_variable_set p) <=
    TSet.cardinal (problem_variable_set q) ->
    problem_size p < problem_size q ->
    unification_problem_order p q.

Inductive result (A B : Type) :=
  | ok : A -> result A B
  | err : B -> result A B.

Arguments ok {A B} _.
Arguments err {A B} _.

Definition result_map {A B C : Type} (f : A -> B) (r : result A C) :
    result B C :=
  match r with
  | ok a => ok (f a)
  | err b => err b
  end.

Inductive unification_error :=
  | different_constructors :
    typeT -> typeT -> unification_error
  | tvarT_occurs :
    TIdent.t -> typeT -> unification_error.

Definition unifies (s : TMap.t typeT) (t u : typeT) :=
  par_tsubst s t = par_tsubst s u.

Definition solves
  (s : TMap.t typeT) (p : unification_problem) :=
    List.Forall (fun c => unifies s (fst c) (snd c)) p.
