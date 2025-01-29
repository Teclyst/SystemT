Require Import Definitions.Type.
Require Import Definitions.Term.

Require Import FSets.FMaps.
Require Import List.

Record t := {
  bmap : list typeT;
  fmap : FMap.t typeT
}.

Definition bMapsTo (n : nat) (u : typeT) (G : t) : Prop :=
  nth_error (Context.bmap G) n = Some u.
  
Definition fMapsTo (x : FIdent.t) (u : typeT) (G : t) : Prop :=
  FMap.MapsTo x u (Context.fmap G).

Definition empty : t := {|
  bmap := List.nil;
  fmap := FMap.empty typeT
|}.

Definition map (f : typeT -> typeT) (G : t) : t := {|
  bmap := List.map f (bmap G);
  fmap := FMap.map f (fmap G)
|}.

Definition context_par_tsubst (s : TMap.t typeT) (G : t) : t := {|
  bmap := List.map (par_tsubst s) (bmap G);
  fmap := fmap G
|}.

Definition bpush (u : typeT) (G : t) : t := {|
  bmap := u :: (bmap G);
  fmap := fmap G
|}.

Definition Equal (G H : t) : Prop :=
  (bmap G) = (bmap H) /\ FMap.Equal (fmap G) (fmap H).

Definition context_tsubst_preorder_with_tsubst
  (s : TMap.t typeT) (G H : t) :
    Prop :=
  (forall (n : nat) (u : typeT),
    bMapsTo n u G -> bMapsTo n (par_tsubst s u) H) /\
  (forall (x : FIdent.t) (u : typeT),
    fMapsTo x u G -> fMapsTo x u H).

Notation "G <|( s ) H" :=
  (context_tsubst_preorder_with_tsubst s G H) (at level 90) :
    system_t_type_scope.

Definition context_tsubst_preorder
  (G H : t) :
    Prop := exists s : TMap.t typeT, G <|(s) H.

Notation "G <| H" :=
  (context_tsubst_preorder G H) (at level 90) :
    system_t_type_scope.
