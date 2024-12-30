Require Import FSets.FMaps.
Require Structures.OrderedType.
Require Import Nat.
Require Import Arith.PeanoNat.
Require Import Arith.Bool_nat.
Require Import String.

Require Import ssreflect ssrfun ssrbool.

Module Type IDENTfun (Map : S).

  Notation t := Map.key.

  Parameter new : forall elt : Type, Map.t elt -> t.

  Axiom new_spec :
      forall elt : Type, forall s : Map.t elt,
      ~ Map.In (new elt s) s.
      
End IDENTfun.

Module Type IDENT.

  Declare Module Map : S.

  Include IDENTfun Map. 

End IDENT.

Module IdentFacts (Import Ident : IDENT).

  Module OTFacts := OrderedTypeFacts Map.E.

  Notation eq := Map.E.eq.

  Notation eqb := OTFacts.eqb.

  Lemma eqb_spec :
      forall x y : t, Bool.reflect (eq x y) (eqb x y).
  Proof.
    intros x y.
    apply Bool.iff_reflect.
    unfold eqb.
    destruct OTFacts.eq_dec;
    constructor;
    auto.
    intro Heq.
    discriminate Heq. 
  Qed.

End IdentFacts.

Module NatMap := FMapList.Make (Structures.OrderedTypeEx.Nat_as_OT).

Module NatIdent <: IDENT.

  Module Map := NatMap.
  
  Definition eqb := Nat.eqb.

  Infix "=?" := eqb (at level 70).

  Definition max {elt} (s : NatMap.t elt) :=
    NatMap.fold (fun x _ acc => Nat.max x acc) s O.
  
  Definition new {elt} (s : NatMap.t elt) :=
    S (max s).

  Lemma max_geq {elt} (s : NatMap.t elt) (x : nat) :
      NatMap.In x s -> max s >= x.
  Proof.
    intro Hin.
    destruct Hin as [e Hmap].
    unfold max.
    rewrite NatMap.fold_1.
    apply NatMap.elements_1 in Hmap.
    generalize O.
    induction Hmap; intro n.
    - destruct H as [Heq _].
      unfold NatMap.E.eq in Heq.
      simpl in Heq.
      simpl.
      rewrite Heq.
      eapply PeanoNat.Nat.le_trans.
    --- exact (PeanoNat.Nat.le_max_l y.1 n).
    --- generalize (Nat.max y.1 n).
        clear n.
        induction l;
        simpl;
        intro n.
    ----- apply PeanoNat.Nat.le_refl.
    ----- eapply PeanoNat.Nat.le_trans.
    ------- exact (PeanoNat.Nat.le_max_r a.1 n).
    ------- exact (IHl (Nat.max a.1 n)).
    - simpl.
      exact (IHHmap (Nat.max y.1 n)).
  Qed.

  Lemma new_spec {elt} (s : NatMap.t elt) :
      ~ NatMap.In (new s) s.
  Proof.
    unfold new.
    intro HIn.
    have : (S (max s)) <= max s.
    - exact (max_geq s (S (max s)) HIn).
    - intro Hleq.
      rewrite <- Nat.lt_succ_r in Hleq.
      exact (Nat.lt_irrefl _ Hleq).
  Qed.

End NatIdent.







