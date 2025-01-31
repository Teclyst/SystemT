Require Import Definitions.Ident.
Require Import Definitions.Term.

Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Init.Wf.

Open Scope system_t_term_scope.

Inductive one_reduction : termT -> termT -> Prop :=
  | redex_beta :
    forall e f : termT,
    one_reduction (appT (absT e) f) (e [|O <- f|])
  | redex_plT_pairT :
    forall e f : termT,
    one_reduction (plT (pairT e f)) e
  | redex_prT_pairT :
    forall e f : termT,
    one_reduction (prT (pairT e f)) f
  | redex_iteT_trueT :
    forall e f : termT,
    one_reduction (iteT trueT e f) e
  | redex_iteT_falseT :
    forall e f : termT,
    one_reduction (iteT falseT e f) f
  | redex_recT_oT :
    forall e f : termT,
    one_reduction (recT e f oT) e
  | redex_recT_sT :
    forall e f g : termT,
    one_reduction (recT e f (sT g)) (appT (appT f (recT e f g)) g)
  | redind_absT :
    forall e f : termT,
    one_reduction e f ->
    one_reduction (absT e) (absT f)
  | redind_appT_l :
    forall e f g : termT,
    one_reduction e f ->
    one_reduction (appT e g) (appT f g)
  | redind_appT_r :
    forall e f g : termT,
    one_reduction f g ->
    one_reduction (appT e f) (appT e g)
  | redind_pairT_l :
    forall e f g : termT,
    one_reduction e f ->
    one_reduction (pairT e g) (pairT f g)
  | redind_pairT_r :
    forall e f g : termT,
    one_reduction f g ->
    one_reduction (pairT e f) (pairT e g)
  | redind_plT :
    forall e f : termT,
    one_reduction e f ->
    one_reduction (plT e) (plT f)
  | redind_prT :
    forall e f : termT,
    one_reduction e f ->
    one_reduction (prT e) (prT f)
  | redind_iteT_l :
    forall e f g h : termT,
    one_reduction e f ->
    one_reduction (iteT e g h) (iteT f g h)
  | redind_iteT_c :
    forall e f g h : termT,
    one_reduction f g ->
    one_reduction (iteT e f h) (iteT e g h)
  | redind_iteT_r :
    forall e f g h : termT,
    one_reduction g h ->
    one_reduction (iteT e f g) (iteT e f h)
  | redind_sT :
    forall e f : termT,
    one_reduction e f ->
    one_reduction (sT e) (sT f)
  | redind_recT_l :
    forall e f g h : termT,
    one_reduction e f ->
    one_reduction (recT e g h) (recT f g h)
  | redind_recT_c :
    forall e f g h : termT,
    one_reduction f g ->
    one_reduction (recT e f h) (recT e g h)
  | redind_recT_r :
    forall e f g h : termT,
    one_reduction g h ->
    one_reduction (recT e f g) (recT e f h).

Notation "e ->1 f" := (one_reduction e f) (at level 70) : system_t_term_scope.

Inductive reduction : nat -> termT -> termT -> Prop :=
  | red_refl_zero : forall e : termT, reduction O e e
  | red_next :
    forall n : nat, forall e f g : termT,
    (e ->1 f) -> reduction n f g -> 
    reduction (S n) e g.

Notation "e ->( n ) f" := (reduction n e f) (at level 70) : system_t_term_scope.

Definition reduction_star (e f : termT) : Prop :=
    exists n : nat, e ->(n) f.

Notation "e ->* f" := (reduction_star e f) (at level 70) : system_t_term_scope.

Inductive equivalence : termT -> termT -> Prop :=
  | red_eq_red : forall e f : termT,
    e ->* f -> equivalence e f
  | red_eq_symm : forall e f : termT,
    equivalence e f -> equivalence f e
  | red_eq_trans : forall e f g : termT,
    equivalence e f ->
    equivalence f g ->
    equivalence e g.

Notation "e === f" := (equivalence e f) (at level 70) : system_t_term_scope.

Definition reducible (e : termT) : Prop :=
    exists f : termT, e ->1 f.

Definition normal_form (e : termT) : Prop :=
    ~ reducible e.

Fixpoint reducibleb (e : termT) : bool :=
  match e with
  | appT (absT _) _
  | plT (pairT _ _)
  | prT (pairT _ _)
  | iteT trueT _ _
  | iteT falseT _ _
  | recT _ _ oT
  | recT _ _ (sT _) => true
  | absT e
  | plT e
  | prT e
  | sT e => reducibleb e
  | appT e f
  | pairT e f => reducibleb e || reducibleb f
  | iteT e f g
  | recT e f g => reducibleb e || reducibleb f || reducibleb g
  | _ => false
  end.

Fixpoint left_reduce (e : termT) : option termT :=
  match e with
  | appT (absT e) f => Some (e [|O <- f|])
  | plT (pairT e f) => Some e
  | prT (pairT e f) => Some f
  | iteT trueT e f => Some e
  | iteT falseT e f => Some f 
  | recT e f oT => Some e
  | recT e f (sT g) => Some (appT (appT f (recT e f g)) g)
  | absT e => option_map absT (left_reduce e)
  | plT e => option_map plT (left_reduce e)
  | prT e => option_map prT (left_reduce e)
  | sT e => option_map sT (left_reduce e)
  | appT e f =>
    match left_reduce e, left_reduce f with
    | Some e, _ => Some (appT e f)
    | _, Some f => Some (appT e f)
    | _, _ => None
    end
  | pairT e f =>
    match left_reduce e, left_reduce f with
    | Some e, _ => Some (pairT e f)
    | _, Some f => Some (pairT e f)
    | _, _ => None
    end
  | iteT e f g =>
    match left_reduce e, left_reduce f, left_reduce g with
    | Some e, _, _ => Some (iteT e f g)
    | _, Some f, _ => Some (iteT e f g)
    | _, _, Some g => Some (iteT e f g)
    | _, _, _ => None
    end
  | recT e f g =>
    match left_reduce e, left_reduce f, left_reduce g with
    | Some e, _, _ => Some (recT e f g)
    | _, Some f, _ => Some (recT e f g)
    | _, _, Some g => Some (recT e f g)
    | _, _, _ => None
    end
  | _ => None
  end.

Definition reduction_one (e f : termT) : Prop := f ->1 e.

Notation "e 1<- f" := (reduction_one e f) (at level 70) : system_t_term_scope.

Definition strongly_normalizing (e : termT) : Prop := Acc reduction_one e.
