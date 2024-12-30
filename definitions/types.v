Declare Scope system_t_type_scope.

Require Import Nat.
Require Import ident.

Declare Module TIdent : IDENT.

Module TIdentFacts := IdentFacts TIdent.

Infix "=?t" := TIdentFacts.eqb (at level 70).

Definition tident := TIdent.t.

Inductive typeT :=
  | natT : typeT
  | boolT : typeT
  | tvarT : tident -> typeT
  | funT : typeT -> typeT -> typeT.

Notation "t ->T u" := (funT t u) (at level 80, right associativity).

Fixpoint tvarT_subst (x : tident) (t a : typeT) :=
  match t with
  | tvarT y =>
    match x =?t y with
    | true => a
    | _ => tvarT y
    end
  | funT t u =>
    funT (tvarT_subst x t a) (tvarT_subst x u a)
  | t =>
    t
  end.