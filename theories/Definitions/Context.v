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
  
Definition fMapsTo (x : fident) (u : typeT) (G : t) : Prop :=
  FMap.MapsTo x u (Context.fmap G).

Definition empty : t := {|
  bmap := List.nil;
  fmap := FMap.empty typeT
|}.

Definition map (f : typeT -> typeT) (G : t) := {|
  bmap := List.map f (bmap G);
  fmap := FMap.map f (fmap G)
|}.

Definition context_par_tsubst (s : TMap.t typeT) : t -> t :=
  map (typeT_par_tsubst s).

Definition bpush (u : typeT) (G : t) := {|
  bmap := u :: (bmap G);
  fmap := fmap G
|}.

Definition Equal (G H : t) :=
  (bmap G) = (bmap H) /\ FMap.Equal (fmap G) (fmap H).
