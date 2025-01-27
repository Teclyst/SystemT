Require Import Nat.
Require Import Definitions.Ident.

Declare Scope system_t_type_scope.
Open Scope system_t_type_scope.

Module TIdent <: IDENT := StringIdent.

Module TMap := TIdent.Map.

Module TMapFacts := Coq.FSets.FMapFacts.WFacts TMap.

Module TIdentFacts := IdentFacts TIdent.

Inductive typeT :=
  | natT : typeT
  | boolT : typeT
  | tvarT : TIdent.t -> typeT
  | funT : typeT -> typeT -> typeT
  | prodT : typeT -> typeT -> typeT.

Notation "t ->T u" := (funT t u) (at level 80, right associativity) : system_t_type_scope.

Notation "t *T u" := (prodT t u) (at level 65, left associativity) : system_t_type_scope.

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
