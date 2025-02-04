Require Import FSets.FSets.
Require Import FSets.FMaps.
Require Import FSets.FMapAVL.
Require Structures.OrderedType.
Require Import PeanoNat.
Require Import Nat.
Require Import Ascii.
Require Import String.

Require Import ssreflect ssrfun ssrbool.

Module Type IDENTfun (E : UsualOrderedType).

  Notation t := E.t.

  Parameter new : list t -> t.

  Axiom new_spec : forall l : list t, ~ In (new l) l.

End IDENTfun.

Module Type IDENT.

  Declare Module E : UsualOrderedType.

  Include IDENTfun E. 

End IDENT.

Module IdentFacts (Import Ident : IDENT)
  (IdentSet : FSets.FSetInterface.S
    with Definition E.t := Ident.E.t
    with Definition E.eq := Ident.E.eq)
  (IdentMap : FSets.FMapInterface.S
    with Definition E.t := Ident.E.t
    with Definition E.eq := Ident.E.eq).

  Include OrderedTypeFacts E.

  Lemma eqb_spec {x y : t} : Bool.reflect (eq x y) (eqb x y).
  Proof.
    destruct eqb eqn:Heq;
    unfold eqb in Heq;
    destruct eq_dec;
    try discriminate Heq;
    try left;
    try right;
    assumption. 
  Qed.

  Lemma eqb_refl {x : t} : eqb x x = true.
  Proof.
    apply/ eqb_spec.
    reflexivity.
  Qed.

  Lemma in_iff_inA_eq {A : Type} {a : A} {l : list A} :
    InA eq a l <-> In a l.
  Proof.
    constructor; 
    move=> Hin.
    - induction Hin;
      simpl.
    --- left.
        symmetry.
        assumption.
    --- right.
        assumption.
    - induction l.
    --- destruct Hin.
    --- destruct Hin as [Heq | Hin].
    ----- left.
          symmetry.
          assumption.
    ----- right.
          auto.
  Qed.

  Definition set_new (s : IdentSet.t) :=
    new (IdentSet.elements s).

  Lemma set_new_spec {s : IdentSet.t} :
    ~ IdentSet.In (set_new s) s.
  Proof.
    move=> Hin.
    apply IdentSet.elements_1 in Hin.
    rewrite in_iff_inA_eq in Hin.
    destruct (new_spec _ Hin).
  Qed.

  Definition map_new {A : Type} (s : IdentMap.t A) :=
    new (List.map fst (IdentMap.elements s)).

  Lemma in_iff_inA_eq_key_elt {A : Type} {a : t * A} {l : list (t * A)} :
    InA (@IdentMap.eq_key_elt A) a l <-> In a l.
  Proof.
    constructor; 
    move=> Hin.
    - induction Hin;
      simpl.
    --- left.
        symmetry.
        destruct a as [a b].
        destruct y as [c d].
        destruct H as [Heq1 Heq2].
        f_equal;
        assumption.
    --- right.
        assumption.
    - induction l.
    --- destruct Hin.
    --- destruct Hin as [Heq | Hin].
    ----- left.
          destruct a as [a b].
          destruct a0 as [c d].
          inversion Heq.
          constructor;
          reflexivity.
    ----- right.
          auto.
  Qed.

  Lemma map_new_spec {A : Type} {s : IdentMap.t A} :
    ~ IdentMap.In (map_new s) s.
  Proof.
    move=> [a Hmap].
    apply IdentMap.elements_1 in Hmap.
    unfold map_new in Hmap.
    rewrite in_iff_inA_eq_key_elt in Hmap.
    apply (in_map fst) in Hmap.
    simpl in Hmap.
    destruct (new_spec _ Hmap).
  Qed.

  Definition new_map (s t : list Ident.t) : IdentMap.t Ident.t :=
    (List.fold_right
      (fun x acc =>
        let y := new acc.2 in
        (IdentMap.add x y acc.1, y :: acc.2))
      (IdentMap.empty Ident.t, s ++ t)
      t).1.

  Lemma new_map_spec_1 {s t : list Ident.t} {x y : Ident.t} :
      IdentMap.MapsTo x y (new_map s t) ->
      ~ In y (s ++ t).
  Proof.
  Admitted.

  Lemma set_new_map_spec_2 {s t : list Ident.t} {w x y z : Ident.t} :
      IdentMap.MapsTo w x (new_map s t) ->
      IdentMap.MapsTo y z (new_map s t) -> x = z ->
      w = y.
  Proof.
  Admitted.

  Lemma set_new_map_spec_3 {s t : list Ident.t} {x : Ident.t} :
      In x s -> IdentMap.In x (new_map s t).
  Proof.
  Admitted.

End IdentFacts.

Module Nat_as_OT <: UsualOrderedType :=
  Structures.OrderedTypeEx.Nat_as_OT.

Module NatSet : FSets.FSetInterface.S
  with Definition E.t := nat
  with Definition E.eq := @eq nat :=
  FSets.FSetAVL.Make Nat_as_OT.

Module NatMap : FSets.FMapInterface.S
  with Definition E.t := nat
  with Definition E.eq := @eq nat :=
  FSets.FMapAVL.Make Nat_as_OT.

Module NatIdent <: IDENT.

  Module E := Nat_as_OT.

  Notation t := nat.

  Definition eqb := Nat.eqb.

  Infix "=?" := eqb (at level 70).

  Definition max (l : list nat) :=
    List.fold_right (fun x acc => Nat.max x acc) O l.

  Definition new (l : list nat) :=
    S (max l).

  Lemma max_geq (l : list nat) (n : nat) :
      In n l -> n <= max l.
  Proof.
    move=> Hin.
    induction l.
    destruct Hin.
    simpl;
    destruct Hin.
    - Lia.lia.
    - have Hle := IHl H.
      Lia.lia. 
  Qed.

  Lemma new_spec {l : list nat} :
      ~ In (new l) l.
  Proof.
    intro HIn.
    apply max_geq in HIn.
    unfold new in HIn.
    Lia.lia.
  Qed.

End NatIdent.

Module String_as_OT <: UsualOrderedType :=
  Structures.OrderedTypeEx.String_as_OT.

Module StringSet : FSets.FSetInterface.S
  with Definition E.t := string
  with Definition E.eq := @eq string :=
  FSets.FSetAVL.Make String_as_OT.

Module StringMap : FSets.FMapInterface.S
  with Definition E.t := string
  with Definition E.eq := @eq string :=
  FSets.FMapAVL.Make String_as_OT.

Module StringIdent <: IDENT.

  Open Scope string_scope.

  Module E := String_as_OT.

  Notation t := string.

  Definition eqb := String.eqb.

  Infix "=?" := eqb (at level 70).

  Fixpoint string_of_length (n : nat) : string :=
    match n with
    | O => EmptyString
    | S n => String ("_")%char (string_of_length n)
    end.
  
  Lemma string_of_length_spec {n : nat} :
      length (string_of_length n) = n.
  Proof.
    induction n;
    simpl;
    auto.
  Qed.

  Definition max_length (l : list string) :=
    List.fold_right (fun x acc => Nat.max (length x) acc) O l.

  Definition new (l : list string) :=
    string_of_length (S (max_length l)).

  Lemma max_length_geq {l : list string} {x : string} :
      In x l -> max_length l >= length x.
  Proof.
    move=> Hin.
    induction l.
    destruct Hin.
    simpl;
    destruct Hin.
    - rewrite H.
      Lia.lia.
    - have Hle := IHl H.
      Lia.lia. 
  Qed.

  Lemma new_spec {l : list string} :
      ~ In (new l) l.
  Proof.
    unfold new.
    move=> HIn.
    apply max_length_geq in HIn.
    rewrite string_of_length_spec in HIn.
    Lia.lia.
  Qed.

End StringIdent.
