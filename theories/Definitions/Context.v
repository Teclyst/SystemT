Require Import Definitions.Type.
Require Import Definitions.Term.

Require Import FSets.FMaps.
Require Import List.

(** Typing context. In two parts: a list for bound variables
    as they use de Bruijn indexes, and a map for free variables.    
*)

Record t := {
  bmap : list typeT;
  fmap : FMap.t typeT
}.

Notation "{{ bmap , fmap }}" := {| bmap := bmap; fmap := fmap |} :
    system_t_type_scope.

Definition bMapsTo (n : nat) (u : typeT) (G : t) : Prop :=
  nth_error (bmap G) n = Some u.
  
Definition fMapsTo (x : FIdent.t) (u : typeT) (G : t) : Prop :=
  FMap.MapsTo x u (fmap G).

Definition empty : t := {{nil, FMap.empty typeT}}.

Definition context_par_tsubst (s : TMap.t typeT) (G : t) : t :=
  {{ map (par_tsubst s) (bmap G), fmap G}}.

Notation "G >>c s" :=
  (context_par_tsubst s G) (at level 60) :
    system_t_type_scope.

Definition bpush (u : typeT) (G : t) : t :=
  {{ u :: (bmap G), fmap G }}.

Definition context_tvarT_set (G : t) : TSet.t :=
  fold_right
    (fun t acc => TSet.union (variable_set t) acc) TSet.empty (bmap G).

Definition Equal (G H : t) : Prop :=
  (bmap G) = (bmap H) /\ FMap.Equal (fmap G) (fmap H).

Definition context_order_with_tsubst
  (s : TMap.t typeT) (G H : t) :
    Prop :=
  (forall (n : nat) (u : typeT),
    bMapsTo n u G -> bMapsTo n (u >> s) H) /\
  (forall (x : FIdent.t) (u : typeT),
    fMapsTo x u G -> fMapsTo x u H).

Notation "G >><c( s ) H" :=
  (context_order_with_tsubst s G H) (at level 90) :
    system_t_type_scope.

(** Substitution preorder for contexts. *)
Definition context_order
  (G H : t) :
    Prop := exists s : TMap.t typeT, G >><c(s) H.

Notation "G >><c H" :=
  (context_order G H) (at level 90) :
    system_t_type_scope.
