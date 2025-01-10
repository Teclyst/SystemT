Require Import Nat.
Require Import Definitions.Ident.

Declare Scope system_t_type_scope.
Open Scope system_t_type_scope.

Declare Module TIdent : IDENT.

Module TMap := TIdent.Map.

Module TIdentFacts := IdentFacts TIdent.

Definition tident := TIdent.t.

Inductive typeT :=
  | natT : typeT
  | boolT : typeT
  | tvarT : tident -> typeT
  | funT : typeT -> typeT -> typeT.

Notation "t ->T u" := (funT t u) (at level 80, right associativity) : system_t_type_scope.

Fixpoint typeT_tsubst (x : tident) (a t : typeT) :=
  match t with
  | tvarT y =>
    match TIdentFacts.eqb x y with
    | true => a
    | _ => tvarT y
    end
  | funT t u =>
    funT (typeT_tsubst x a t) (typeT_tsubst x a u)
  | t =>
    t
  end.

Fixpoint typeT_par_tsubst (s : TMap.t typeT) (t : typeT) :=
  match t with
  | tvarT x =>
    match TMap.find x s with
    | Some a => a
    | _ => tvarT x
    end
  | funT t u =>
    funT (typeT_par_tsubst s t) (typeT_par_tsubst s u)
  | t =>
    t
  end.
