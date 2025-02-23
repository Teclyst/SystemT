Require Import FSets.FSets.
Require Import FSets.FMaps.
Require Import FSets.FMapAVL.
Require Import Structures.OrderedType.
Require Import PeanoNat.
Require Import Nat.
Require Import Ascii.
Require Import String.

Require Import ssreflect ssrfun ssrbool.

(** Module specification for variable identifiers.

    Basically, it is an ordered type with a way to create
    fresh variables. It is presented that way to obscure away
    implementation details, which are not very relevant.

    We also provide implementations of the signature for [nat] and
    [string].
*)

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

  Module IdentMapFacts := FSets.FMapFacts.Facts IdentMap.

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

  Definition new_map_aux_list (s t : list Ident.t) : list Ident.t :=
    List.fold_right
      (fun _ l =>
        (new l) :: l)
      (s ++ t)
      t.

  Definition new_map (s t : list Ident.t) : IdentMap.t Ident.t :=
    (List.fold_right
      (fun x acc =>
        let y := new acc.2 in
        (IdentMap.add x y acc.1, y :: acc.2))
      (IdentMap.empty Ident.t, s ++ t)
      t).1.

  Lemma new_map_aux_list_1 {s t : list Ident.t} {x : Ident.t} :
      In x s -> In x (new_map_aux_list s t).
  Proof.
    move: s.
    induction t;
    move=> s;
    unfold new_map_aux_list;
    simpl.
    - rewrite app_nil_r.
      auto.
    - right.
      replace (s ++ a :: t) with ((s ++ a :: nil) ++ t).
      fold (new_map_aux_list (s ++ a :: nil) t).
      apply IHt.
      apply in_or_app.
      left.
      assumption.
      rewrite <- app_assoc.
      reflexivity.
  Qed.

  Lemma new_map_aux_list_2 {s t : list Ident.t} {x : Ident.t} :
      In x t -> In x (new_map_aux_list s t).
  Proof.
    move: s.
    induction t;
    move=> s;
    unfold new_map_aux_list;
    simpl.
    - contradiction.
    - move=> [Heq | Hin];
      replace (s ++ a :: t) with ((s ++ a :: nil) ++ t);
      fold (new_map_aux_list (s ++ a :: nil) t);
      try (
        rewrite <- app_assoc;
        reflexivity;
        fail
      ).
    --- right.
        apply new_map_aux_list_1.
        apply in_or_app.
        right.
        left.
        assumption.
    --- right.
        eauto.
  Qed.

  Lemma new_map_aux_1 {s t : list Ident.t} :
       (List.fold_right
      (fun x acc =>
        (IdentMap.add x (new acc.2) acc.1, (new acc.2) :: acc.2))
      (IdentMap.empty Ident.t, s ++ t)
      t).2 = new_map_aux_list s t.
  Proof.
    move: s.
    induction t;
    unfold new_map_aux_list.
    - auto.
    - move=> s.
      simpl.
      f_equal.
    --- f_equal.
        replace (s ++ a :: t) with ((s ++ a :: nil) ++ t).
    ----- fold (new_map_aux_list (s ++ a :: nil) t).
          auto.
    ----- rewrite <- app_assoc.
          reflexivity.
    --- replace (s ++ a :: t) with ((s ++ a :: nil) ++ t).
    ----- fold (new_map_aux_list (s ++ a :: nil) t).
          auto.
    ----- rewrite <- app_assoc.
          reflexivity.
  Qed.

  Lemma new_map_aux_2 {s t : list Ident.t} {x : Ident.t} :
      (new_map s (x :: t)) =
      IdentMap.add x (new (new_map_aux_list (s ++ x :: nil) t))
        (new_map (s ++ x :: nil) t).
  Proof.
    unfold new_map.
    simpl.
    replace (s ++ x :: t) with ((s ++ x :: nil) ++ t);
    try (rewrite <- app_assoc;
    reflexivity;
    fail).
    rewrite new_map_aux_1.
    reflexivity.
  Qed.

  Lemma new_map_spec_1 {s t : list Ident.t} {x y : Ident.t} :
      IdentMap.MapsTo x y (new_map s t) ->
      ~ In y (s ++ t).
  Proof.
    move: s.
    induction t;
    move=> s Hmap Hin1.
    - unfold new_map in Hmap.
      simpl in Hmap.
      exact (IdentMap.empty_1 Hmap).
    - rewrite new_map_aux_2 in Hmap.
      apply in_app_or in Hin1.
      destruct (eqb a x) eqn:Heq1;
      move/ eqb_spec in Heq1.
    --- have foo : Some y = Some (new (new_map_aux_list (s ++ a :: nil) t)).
        transitivity (IdentMap.find x (IdentMap.add a (new (new_map_aux_list (s ++ a :: nil) t))
(new_map (s ++ a :: nil) t))).
    ----- symmetry.
          auto using IdentMap.find_1.
    ----- apply IdentMap.find_1.
          rewrite Heq1.
          apply IdentMap.add_1.
          reflexivity.
    ----- inversion foo.
          apply (new_spec (new_map_aux_list (s ++ a :: nil) t)).
          rewrite <- H0.
          destruct Hin1 as [Hin1 | Hin1].
    ------- eauto using new_map_aux_list_1, in_or_app.
    ------- apply in_inv in Hin1.
            destruct Hin1 as [Heq2 | Hin1].
    --------- apply new_map_aux_list_1.
              apply in_or_app.
              right.
              left.
              assumption.
    --------- eauto using new_map_aux_list_2.
    --- apply IdentMap.add_3 in Hmap;
        try assumption.
        apply (IHt (s ++ a :: nil) Hmap).
        apply in_or_app.
        destruct Hin1 as [Hin1 | Hin1].
    ----- eauto using in_or_app.
    ----- apply in_inv in Hin1.
          destruct Hin1 as [Heq2 | Hin1].
    ------- left. 
            apply in_or_app.
            right.
            left.
            assumption.
    ------- eauto using new_map_aux_list_2.
  Qed.

  Lemma new_map_spec_aux_3 {s t : list Ident.t} {x : Ident.t} :
      IdentMap.In x (new_map s t) -> In x t.
  Proof.
    move: s.
    induction t;
    move=> s Hin.
    - destruct Hin as [y Hmap].
      unfold new_map in Hmap.
      simpl in Hmap.
      destruct (IdentMap.empty_1 Hmap).
    - simpl.
      rewrite new_map_aux_2 in Hin.
      rewrite IdentMapFacts.add_in_iff in Hin.
      destruct Hin as [Heq | Hin];
      eauto.
  Qed. 

  Lemma new_map_spec_2 {s t : list Ident.t} {x y z : Ident.t} :
      IdentMap.MapsTo x z (new_map s t) ->
      IdentMap.MapsTo y z (new_map s t) ->
      x = y.
  Proof.
    move: s.
    induction t;
    move=> s Hmap1 Hmap2.
    - unfold new_map in Hmap1;
      simpl in Hmap1.
      destruct (IdentMap.empty_1 Hmap1).
    - rewrite new_map_aux_2 in Hmap1, Hmap2.
      destruct (eqb x y) eqn:Heq1;
      move/ eqb_spec in Heq1;
      try assumption.
      apply IdentMap.find_1 in Hmap1, Hmap2.
      destruct (eqb x a) eqn:Heq3;
      move/ eqb_spec in Heq3;
      destruct (eqb y a) eqn:Heq4;
      move/ eqb_spec in Heq4.
    --- destruct Heq1.
        transitivity a;
        auto.
    --- rewrite IdentMapFacts.add_eq_o in Hmap1.
        symmetry.
        assumption.
        rewrite IdentMapFacts.add_neq_o in Hmap2.
        auto.
        inversion Hmap1.
        destruct (new_spec (new_map_aux_list (s ++ a :: nil) t)).
        rewrite H0.
        rewrite <- Heq3.
        rewrite <- Heq3 in Hmap1, Hmap2, H0.
        clear a Heq3 Heq4 Hmap1.
        clear IHt.
        clear H0.
        move: Hmap2.
        generalize (s ++ x :: nil).
        clear x Heq1 s.
        induction t;
        move=> s Hmap2.
    ----- have foo : In y nil.
          apply (new_map_spec_aux_3 (s := s)).
          exists z.
          eauto using IdentMap.find_2.
          destruct foo.
    ----- rewrite new_map_aux_2 in Hmap2.
          destruct (eqb y a) eqn:Heq2;
          move/ eqb_spec in Heq2.
    ------- rewrite IdentMapFacts.add_eq_o in Hmap2.
            symmetry.
            assumption.
            inversion Hmap2.
            unfold new_map_aux_list.
            simpl.
            left;
            f_equal.
            f_equal.
            rewrite <- app_assoc.
            reflexivity.
    ------- unfold new_map_aux_list.
            simpl fold_right.
            replace (s ++ a :: t) with ((s ++ (a :: nil)) ++ t).
    --------- fold (new_map_aux_list (s ++ a :: nil) t).
              right.
              apply IHt;
              rewrite IdentMapFacts.add_neq_o in Hmap2;
              eauto.
    --------- rewrite <- app_assoc.
              reflexivity.
    --- rewrite IdentMapFacts.add_eq_o in Hmap2.
        symmetry.
        assumption.
        rewrite IdentMapFacts.add_neq_o in Hmap1.
        auto.
        inversion Hmap2.
        destruct (new_spec (new_map_aux_list (s ++ a :: nil) t)).
        rewrite H0.
        rewrite <- Heq4.
        rewrite <- Heq4 in Hmap1, Hmap2, H0.
        clear a Heq3 Heq4 Hmap2.
        clear IHt.
        clear H0.
        move: Hmap1.
        generalize (s ++ y :: nil).
        clear y Heq1 s.
        induction t;
        move=> s Hmap1.
    ----- have foo : In x nil.
          apply (new_map_spec_aux_3 (s := s)).
          exists z.
          eauto using IdentMap.find_2.
          destruct foo.
    ----- rewrite new_map_aux_2 in Hmap1.
          destruct (eqb x a) eqn:Heq2;
          move/ eqb_spec in Heq2.
    ------- rewrite IdentMapFacts.add_eq_o in Hmap1.
            symmetry.
            assumption.
            inversion Hmap1.
            unfold new_map_aux_list.
            simpl.
            left;
            f_equal.
            f_equal.
            rewrite <- app_assoc.
            reflexivity.
    ------- unfold new_map_aux_list.
            simpl fold_right.
            replace (s ++ a :: t) with ((s ++ (a :: nil)) ++ t).
    --------- fold (new_map_aux_list (s ++ a :: nil) t).
              right.
              apply IHt;
              rewrite IdentMapFacts.add_neq_o in Hmap1;
              eauto.
    --------- rewrite <- app_assoc.
              reflexivity.
    --- rewrite IdentMapFacts.add_neq_o in Hmap1;
        rewrite IdentMapFacts.add_neq_o in Hmap2;
        eauto using IdentMap.find_2.
  Qed.    

  Lemma set_new_map_spec_3 {s t : list Ident.t} {x : Ident.t} :
      In x t -> IdentMap.In x (new_map s t).
  Proof.
    move: s.
    induction t;
    move=> s Hin.
    - inversion Hin.
    - simpl.
      unfold new_map in IHt.
      simpl in IHt.
      unfold new_map.
      simpl.
      simpl in Hin.
      destruct (eqb a x) eqn:Heq1;
      move/ eqb_spec in Heq1.
    --- exists ((new
        (fold_right
        (fun (x0 : IdentMap.key) (acc : IdentMap.t Ident.t * list Ident.t) =>
        (IdentMap.add x0 (new acc.2) acc.1, new acc.2 :: acc.2))
        (IdentMap.empty Ident.t, s ++ a :: t) t).2)).
        apply IdentMap.add_1.
        assumption.
    --- destruct Hin as [Heq | Hin];
        try contradiction.
        destruct (IHt (s ++ a :: nil)) as [y Hmap];
        try assumption.
        exists y.
        apply IdentMap.add_2.
        assumption.
        rewrite <- app_assoc in Hmap.
        simpl in Hmap.
        assumption.
Qed.

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
