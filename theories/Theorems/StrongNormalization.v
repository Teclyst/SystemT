Require Import Nat.
Require Import PeanoNat.
Require Import Logic.Decidable.
Require Import Coq.Arith.Compare_dec.
Require Import Definitions.Ident.
Require Import Definitions.Term.
Require Import Definitions.Type.
Require Import Definitions.Typing.
Require Import Definitions.Reduction.
Require Import Theorems.Substitution.
Require Import Theorems.Reduction.
Require Import Theorems.NormalForm.
Require Import Morphisms.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_term_scope.
Open Scope system_t_type_scope.

(**
  We will later want to build elements of reducibility candidates.
  To avoid issues with bound variables gettting captured, we'll use
  one free variable instead.
   
  However, free variables idents are defined through an abstract
  signature to be generic, so we can't just find an example... or so
  it would seem. Indeed, we have the [Fident.new] function, which
  can be used over an empty [Fmap.t] to produce a default [fident].

  (For the current implementation for [nat] and [string], it would
  respectively be [1] and ["_"].)
*)
Definition default_fident := FIdent.new _ (FMap.empty unit).

Lemma normal_form_strongly_normalizing {e : termT} :
    normal_form e -> strongly_normalizing e.
Proof.
  intro Hnf.
  constructor.
  intros f Hred.
  destruct Hnf.
  exists f.
  assumption.
Qed.

Lemma strongly_normalizing_f {e : termT} {r : termT -> termT} :
    (forall e f : termT, (r e ->1 r f) -> (e ->1 f)) ->
    (forall e f : termT, (r e ->1 f) -> exists g : termT, f = r g) ->
    strongly_normalizing e ->
    strongly_normalizing (r e).
Proof.
  move=> Himpl Hsur Hsn.
  induction Hsn as [f Hacc Hred1].
  constructor.
  move=> g Hred2.
  destruct (Hsur _ _ Hred2) as [h Heq].
  rewrite Heq.
  apply Hred1.
  apply Himpl.
  rewrite Heq in Hred2.
  assumption. 
Qed.

Lemma strongly_normalizing_f_inv {e : termT} {r : termT -> termT} :
    (forall e f : termT, (e ->1 f) -> (r e ->1 r f)) ->
    strongly_normalizing (r e) ->
    strongly_normalizing e.
Proof.
  generalize (eq_refl (r e)).
  pattern (r e) at -1.
  generalize (r e) at -2.
  simpl.
  move=> f Heq Himpl Hsn.
  rewrite <- Heq in Hsn.
  move: e Heq.
  induction Hsn as [f Hacc Hred1].
  move=> e Heq.
  constructor.
  move=> g Hred2.
  eapply Hred1.
  - unfold "1<-".
    rewrite Heq.
    apply Himpl.
    exact Hred2.
  - reflexivity.
Qed.

Lemma strongly_normalizing_absT_inv {e : termT} :
    strongly_normalizing (absT e) ->
    strongly_normalizing e.
Proof.
  apply strongly_normalizing_f_inv.
  eauto using one_reduction.
Qed.

Lemma strongly_normalizing_appT_inv_l {e f : termT} :
    strongly_normalizing (appT e f) ->
    strongly_normalizing e.
Proof.
  apply (strongly_normalizing_f_inv (r := (fun e => appT e f))).
  eauto using one_reduction.
Qed.

Lemma strongly_normalizing_appT_inv_r {e f : termT} :
    strongly_normalizing (appT e f) ->
    strongly_normalizing f.
Proof.
  apply strongly_normalizing_f_inv.
  eauto using one_reduction.
Qed.

Lemma strongly_normalizing_bsubst_inv {e f : termT} {n : nat} :
    strongly_normalizing (e[n <- f]) ->
    strongly_normalizing e.
Proof.
  apply (strongly_normalizing_f_inv (r := fun e => e [n <- f])).
  eauto using one_reduction_bsubst_l.
Qed.

Lemma strongly_normalizing_par_fsubst_inv {e : termT} {s : FMap.t termT} :
    strongly_normalizing (par_fsubst s e) ->
    strongly_normalizing e.
Proof.
  apply strongly_normalizing_f_inv.
  eauto using one_reduction_par_fsubst.
Qed.

Lemma strongly_normalizing_one_reduction {e f : termT} :
    (e ->1 f) -> strongly_normalizing e ->
    strongly_normalizing f.
Proof.
  move=> Hred Hsn.
  destruct Hsn.
  apply H.
  assumption.
Qed.

Lemma strongly_normalizing_reduction {n : nat} {e f : termT} :
    (e ->(n) f) -> strongly_normalizing e ->
    strongly_normalizing f.
Proof.
  move=> Hred.
  induction Hred;
  auto.
  move=> Hsn.
  apply IHHred.
  apply (strongly_normalizing_one_reduction (e := e));
  assumption.
Qed.

Lemma strongly_normalizing_reduction_star {e f : termT} :
    (e ->* f) -> strongly_normalizing e ->
    strongly_normalizing f.
Proof.
  move=> [n Hred].
  exact (strongly_normalizing_reduction Hred).
Qed.

Lemma strongly_normalizing_redex_beta_inv {e f : termT} :
    strongly_normalizing (e[O <- f]) ->
    strongly_normalizing f ->
    strongly_normalizing (appT (absT e) f).
Proof.
  move=> Hsnsbst.
  have Hsne := strongly_normalizing_bsubst_inv Hsnsbst.
  move: Hsnsbst.
  move: f.
  induction Hsne as [e Hsne Hinde].
  move=> f Hsnsbst Hsnf.
  move: Hinde Hsne Hsnsbst.
  move: e.
  induction Hsnf as [f Hsnf Hindf].
  move=> e Hinde Hsne Hsnsbst. 
  constructor.
  move=> g Hred.
  inversion Hred; auto.
  - inversion H2.
    apply Hinde.
  --- unfold "1<-".
      assumption.
  --- eapply strongly_normalizing_reduction_star.
  ----- eapply reduction_star_bsubst_l.
        apply one_reduction_reduction_star.
        exact H4.
  ----- assumption.
  --- constructor.
      assumption.
  - apply Hindf.    
  --- unfold "1<-".
      assumption.
  --- assumption.
  --- exact Hsne.
  --- eapply strongly_normalizing_reduction_star.
  ----- eapply reduction_star_bsubst_r.
        apply one_reduction_reduction_star.
        exact H2.
  ----- assumption. 
Qed.

Fixpoint reducibility_candidate (t : typeT) : termT -> Prop :=
  match t with
  | boolT =>
    fun e =>
      strongly_normalizing e /\ (exists b : bool, e ->* bool_as_boolT b)
  | natT =>
    fun e =>
      strongly_normalizing e /\ (exists n : nat, e ->* nat_as_natT n)
  | tvarT t =>
    strongly_normalizing
  | funT t u =>
    fun e =>
      forall f : termT,
      reducibility_candidate t f ->
      reducibility_candidate u (appT e f)
  end.

Lemma reducibility_candidate_one_reduction {t : typeT} {e f : termT} :
    (e ->1 f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  move: e f.
  induction t; simpl; move=> e f Hred Hredue.
  - destruct Hredue as [Hsne [n Hredn]].
    constructor.
  --- apply Hsne.
      exact Hred.
  --- exists n.
      eapply normal_form_reduction_star_confluence.
  ----- exact normal_form_nat_as_natT.
  ----- apply one_reduction_reduction_star.
        exact Hred.
  ----- assumption.
  - destruct Hredue as [Hsne [b Hredb]].
    constructor.
  --- apply Hsne.
      exact Hred.
  --- exists b.
      eapply normal_form_reduction_star_confluence.
  ----- exact normal_form_bool_as_boolT.
  ----- apply one_reduction_reduction_star.
        exact Hred.
  ----- assumption.
  - apply Hredue.
    assumption.
  - move=> g Hredug.
    apply (IHt2 (appT e g));
    auto using one_reduction.
Qed.

Lemma reducibility_candidate_reduction {t : typeT} {e f : termT} {n : nat} :
    (e ->(n) f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  move=> Hred.
  induction Hred;
  eauto using reducibility_candidate_one_reduction.
Qed.

Lemma reducibility_candidate_reduction_star {t : typeT} {e f : termT} :
    (e ->* f) -> reducibility_candidate t e -> reducibility_candidate t f.
Proof.
  intro Hred.
  destruct Hred.
  eauto using reducibility_candidate_reduction.
Qed.    

Fixpoint head_appT_list (l : list termT) (e : termT) : termT :=
  match l with
  | nil => e
  | cons f l => appT (head_appT_list l e) f
  end.

Lemma head_appT_list_one_reduction {e f : termT} {l : list termT} :
    (e ->1 f) -> (head_appT_list l e ->1 head_appT_list l f).
Proof.
  induction l;
  eauto using one_reduction.
Qed.

Lemma head_appT_list_reduction {e f : termT} {l : list termT} {n : nat} :
    (e ->(n) f) -> (head_appT_list l e ->(n) head_appT_list l f).
Proof.
  move=> Hred.
  induction Hred;
  eauto using reduction, head_appT_list_one_reduction.
Qed.

Lemma head_appT_list_reduction_star {e f : termT} {l : list termT} :
    (e ->* f) -> (head_appT_list l e ->* head_appT_list l f).
Proof.
  move=> [n Hred].
  exists n.
  auto using head_appT_list_reduction.
Qed.

Lemma head_appT_list_strongly_normalizing_inv {e : termT} {l : list termT} :
    strongly_normalizing (head_appT_list l e) -> strongly_normalizing e.
Proof.
  apply strongly_normalizing_f_inv.
  move=> f g.
  exact head_appT_list_one_reduction.
Qed.

Definition neutral (e : termT) := forall f : termT, e <> absT f. 

Inductive relation_exponentiation_one {A : Type} (r : A -> A -> Prop) :
  list A -> list A -> Prop :=
  | relation_exponentiation_one_in :
    forall a b : A, forall l : list A,
    r a b -> relation_exponentiation_one r (a :: l) (b :: l)
  | relation_exponentiation_one_cons :
    forall a : A, forall l m : list A,
    relation_exponentiation_one r l m ->
    relation_exponentiation_one r (a :: l) (a :: m).

Lemma relation_exponentiation_one_length
  {A : Type} {r : A -> A -> Prop} {l m : list A} :
  relation_exponentiation_one r l m -> List.length l = List.length m.
Proof.
  move=> Hrelexp.
  induction Hrelexp;
  simpl;
  try rewrite IHHrelexp;
  auto.
Qed.

Lemma relation_exponentiation_forall_Acc
  {A : Type} {r : A -> A -> Prop} {l m : list A} :
  relation_exponentiation_one r l m ->
  List.Forall (Acc r) m ->
  List.Forall (Acc r) l.
Proof.
  move=> Hrelexp.
  induction Hrelexp;
  move=> Hfor;
  inversion Hfor.
  - constructor;
    destruct H2 as [Hacc];
    try apply Hacc;
    assumption.
  - auto.
Qed.

Lemma head_appT_list_reduction_exponentiation_one
  {e : termT} {l m : list termT} :
    relation_exponentiation_one (reduction_one) m l ->
    (head_appT_list l e ->1 head_appT_list m e).
Proof.
  move=> Hrelexp.
  induction Hrelexp;
  eauto using one_reduction.
Qed.

Lemma relation_exponentiation_one_Acc
  {A : Type} {r : A -> A -> Prop} {l : list A} :
  List.Forall (Acc r) l -> Acc (relation_exponentiation_one r) l.
Proof.
  generalize (eq_refl (List.length l)).
  pattern (List.length l) at -1.
  generalize (List.length l) at -2.
  move=> n.
  move: l.
  induction n.
  - move=> l Hlen.
    destruct l;
    try discriminate Hlen.
    constructor.
    move=> l Hred.
    inversion Hred.
  - move=> l Hlen Hfor.
    destruct l;
    try discriminate Hlen.
    inversion Hlen.
    inversion Hfor.
    have foo := IHn l H0 H3.
    clear Hlen H1 l0 H x.
    move: a H2 Hfor.
    induction foo.
    move=> a Hacc.
    induction Hacc.
    constructor.
    move=> m Hrelexp.
    inversion Hrelexp.
  --- apply H4.
  ----- assumption.
  ----- constructor;
        try assumption.
        inversion Hfor.
        destruct H11.
        apply H11.
        assumption.
  --- apply H1.
  ----- assumption.
  ----- have bar := relation_exponentiation_one_length Hrelexp.
        rewrite <- H6 in bar.
        inversion bar.
        rewrite H10.
        assumption.
  ----- apply (relation_exponentiation_forall_Acc (m := x));
        assumption.
  ----- inversion Hfor.
        assumption.
  ----- apply (relation_exponentiation_forall_Acc (m := x0 :: x)).
  ------- constructor;
          assumption.
  ------- assumption.
Qed.

Inductive relation_product
  {A B : Type} (r : A -> A -> Prop) (s : B -> B -> Prop) :
    (A * B) -> (A * B) -> Prop :=
  | relation_product_left : forall a b : A, forall c : B,
    r a b -> relation_product r s (a, c) (b, c)
  | relation_product_right : forall a : A, forall b c : B,
    s b c -> relation_product r s (a, b) (a, c).

Inductive relation_restriction
  {A : Type} (P : A -> Prop) (r : A -> A -> Prop) :
    {x : A | P x} -> {x : A | P x} -> Prop :=
  | relation_restriction_intro : forall (x y : A) (hx : P x) (hy : P y),
    r x y -> relation_restriction P r (exist P x hx) (exist P y hy).

Lemma relation_product_Acc
  {A B : Type} {r : A -> A -> Prop} {s : B -> B -> Prop} {a : A} {b : B} :
    Acc r a -> Acc s b -> Acc (relation_product r s) (a, b).
Proof.
  move=> Hacc1.
  move: b.
  induction Hacc1.
  move=> b Hacc2.
  move: x H H0.
  induction Hacc2.
  move=> y Hacc1 Hind.
  constructor.
  move=> [a b] Hrelprod.
  inversion Hrelprod;
  auto.
  - rewrite <- H5.
    apply Hind.
    assumption.
    rewrite H5.
    constructor.
    assumption.
Qed.

Lemma relation_restriction_Acc
  {A : Type} {P : A -> Prop} {r : A -> A -> Prop} {a : A} {ha : P a} :
    Acc r a -> Acc (relation_restriction P r) (exist P a ha).
Proof.
  move=> Hacc.
  induction Hacc.
  constructor.
  move=> [a Ha] Hrelres.
  inversion Hrelres;
  auto.
Qed.

Lemma strongly_normalizing_gen
    {A B : Type}
    {f g : A -> B -> termT}
    {r : B -> B -> Prop} {a : A} {b : B}:
    (forall (a : A) (b : B) (e : termT), (f a b ->1 e) ->
      (exists c : B, r c b /\ e = f a c /\ g a b ->* g a c) \/
      (exists c : A, e = f c b /\ g a b ->1 g c b) \/
        g a b ->* e) ->
    Acc r b -> strongly_normalizing (g a b) ->
    strongly_normalizing (f a b).
Proof.
  move=> Hneeded Hacc1.
  move: a.
  induction Hacc1.
  move=> a Hsn.
  unfold strongly_normalizing in Hsn.
  generalize (eq_refl (g a x)).
  generalize (g a x) at -2.
  move=> t Heq.
  rewrite <- Heq in Hsn.
  move: a x Heq H H0.
  induction Hsn.
  move=> a b Heq Hfacc Hind.
  constructor.
  move=> e Hred.
  destruct (Hneeded a b e Hred) as [[c [Hr [Heq2 Hred2]]] | [[c [Heq2 Hred2]] | Hred2]].
  - rewrite Heq2.
    apply Hind;
    try assumption.
    eapply strongly_normalizing_reduction_star.
    exact Hred2.
    rewrite <- Heq.
    constructor.
    assumption.
  - rewrite Heq2.
    apply (H0 (g c b));
    auto.
    rewrite Heq.
    assumption.
  - eapply strongly_normalizing_reduction_star.
    exact Hred2.
    rewrite <- Heq.
    constructor.
    assumption.
Qed.

Lemma head_appT_neutral {e : termT} {l : list termT} :
  neutral e -> neutral (head_appT_list l e).
Proof.
  move=> Hneut f Heq.
  destruct l;
  simpl in Heq.
  - apply (Hneut f).
    assumption.
  - discriminate Heq.
Qed. 

Lemma head_appT_neutral_good {e f : termT} {l : list termT} :
  neutral e -> (head_appT_list l e ->1 f) ->
  (exists g : termT, e ->1 g /\ f = head_appT_list l g) \/
  (exists m : list termT,
    relation_exponentiation_one reduction_one m l /\
    f = head_appT_list m e).
Proof.
  move: e f.
  induction l;
  move=> e f Hneut Hred1.
  - left.
    eauto.
  - simpl in Hred1.
    inversion Hred1.
  --- symmetry in H0.
      destruct ((head_appT_neutral Hneut) e0 H0).
  --- destruct (IHl e f0 Hneut H2) as [[h [Hred2 Heq2]] | [m [Hred2 Heq2]]].
  ----- left.
        exists h.
        constructor.
  ------- assumption.
  ------- rewrite Heq2.
          reflexivity.
  ----- right.
        exists (a :: m)%list.
        constructor.
  ------- right.
          assumption.
  ------- rewrite Heq2.
          reflexivity.
  --- right.
      exists (g :: l)%list.
      constructor.
  ----- left.
        assumption.
  ----- reflexivity.   
Qed. 

Lemma head_appT_list_strongly_normalizing_inv_2 {e : termT} {l : list termT} :
    strongly_normalizing (head_appT_list l e) ->
    List.Forall strongly_normalizing l.
Proof.
  induction l;
  simpl.
  - auto using List.Forall.
  - move=> Hsn.
    constructor.
  --- apply (strongly_normalizing_appT_inv_r Hsn).
  --- apply IHl.
      apply (strongly_normalizing_appT_inv_l Hsn).
Qed.    

Lemma TODO : forall p : Prop, p.
Proof. Admitted. 

Lemma head_appT_strongly_normalizing_gen
    {A B : Type}
    {f g : A -> B -> termT}
    {r : B -> B -> Prop} {a : A} {b : B}
    {l : list termT} :
    (forall (a : A) (b : B) (e : termT), (f a b ->1 e) ->
      (exists c : B, r c b /\ e = f a c /\ g a b ->* g a c) \/
      (exists c : A, e = f c b /\ g a b ->1 g c b) \/
        g a b ->* e) ->
    (forall (a : A) (b : B), neutral (f a b)) ->
    Acc r b -> strongly_normalizing (head_appT_list l (g a b)) ->
    strongly_normalizing (head_appT_list l (f a b)).
Proof.
  move=> Hneeded Hneutral Hacc Hsn.
  apply (strongly_normalizing_gen
    (f := fun (a : A) (c : B * list termT) => head_appT_list c.2 (f a c.1))
    (g := fun (a : A) (c : B * list termT) => head_appT_list c.2 (g a c.1))
    (r := relation_product r (relation_exponentiation_one reduction_one))
    (a := a)
    (b := (b, l))); auto.
  - move=> c [d m] e Hred.
    simpl in Hred.
    simpl.
    destruct (head_appT_neutral_good (Hneutral c d) Hred) as [[h [Hred2 Heq2]] | [o [Hred2 Heq2]]].
  --- destruct (Hneeded c d h Hred2) as [[i [Hr [Heq3 Hred3]]] | [[i [Heq3 Hred3]] | Hred3]].
  ----- left.
        exists (i, m).
        constructor.
  ------- apply relation_product_left.
          assumption.
  ------- constructor.
  --------- simpl.
            rewrite Heq3 in Heq2.
            assumption.
  --------- simpl.
            apply head_appT_list_reduction_star. 
            assumption.
  ----- right.
        left.
        exists i.
        constructor.
  ------- rewrite Heq3 in Heq2.
          assumption.
  ------- apply head_appT_list_one_reduction.
          assumption.
  ----- right.
        right.
        rewrite Heq2.
        apply head_appT_list_reduction_star.
        assumption.
  --- left.
      exists (d, o).
      constructor.
  ----- apply relation_product_right.
        assumption.
  ----- simpl.
        constructor.
  ------- assumption.
  ------- apply one_reduction_reduction_star.
          apply head_appT_list_reduction_exponentiation_one.
          assumption.
  - apply relation_product_Acc; auto.
    apply relation_exponentiation_one_Acc.
    apply (head_appT_list_strongly_normalizing_inv_2 Hsn).
Qed.

Lemma head_appT_list_beta_strongly_normalizing {e f : termT} {l : list termT} :
    strongly_normalizing (head_appT_list l (e[O <- f])) ->
    strongly_normalizing f ->
    strongly_normalizing (head_appT_list l (appT (absT e) f)).
Proof.
  move=> Hsn1 Hsn2.
  apply (head_appT_strongly_normalizing_gen
    (f := fun e f => appT (absT e) f)
    (g := bsubst O)
    (r := reduction_one)); auto.
  - move=> a b g Hred.
    inversion Hred.
  --- right.
      right.
      reflexivity.
  --- right.
      left.
      inversion H2.
      exists f1.
      constructor.
  ----- reflexivity.
  ----- apply one_reduction_bsubst_l.
        assumption.
  --- left.
      exists g0.
      constructor.
  ----- assumption.
  ----- constructor.
  ------- reflexivity.
  ------- apply reduction_star_bsubst_r.
          apply one_reduction_reduction_star.
          assumption.
  - move=> a b c Heq.
    discriminate Heq.
Qed.

Lemma head_appT_list_iteT_falseT_strongly_normalizing
  {e f : termT} {l : list termT} :
    strongly_normalizing (head_appT_list l f) ->
    strongly_normalizing e ->
    strongly_normalizing (head_appT_list l (iteT falseT e f)).
Proof.
  move=> Hsn1 Hsn2.
  apply (head_appT_strongly_normalizing_gen
    (f := fun f e => iteT falseT e f)
    (g := fun f e => f)
    (r := reduction_one)); auto.
  - move=> a b g Hred.
    inversion Hred.
  --- right.
      right.
      reflexivity.
  --- inversion H3.
  --- left.
      exists g0.
      constructor.
  ----- assumption.
  ----- constructor;
        reflexivity. 
  --- right.
      left.
      exists h.
      constructor;
      auto.
  - move=> a b c Heq.
    discriminate Heq.
Qed.

Lemma head_appT_list_iteT_trueT_strongly_normalizing
  {e f : termT} {l : list termT} :
    strongly_normalizing (head_appT_list l e) ->
    strongly_normalizing f ->
    strongly_normalizing (head_appT_list l (iteT trueT e f)).
Proof.
  move=> Hsn1 Hsn2.
  apply (head_appT_strongly_normalizing_gen
    (f := fun e f => iteT trueT e f)
    (g := fun e f => e)
    (r := reduction_one)); auto.
  - move=> a b g Hred.
    inversion Hred.
  --- right.
      right.
      reflexivity.
  --- inversion H3.
  --- right.
      left.
      exists g0.
      constructor;
      auto.
  --- left.
      exists h.
      constructor.
  ----- assumption.
  ----- constructor;
        reflexivity. 
  - move=> a b c Heq.
    discriminate Heq.
Qed.

Lemma head_appT_list_iteT_strongly_normalizing
  {e f g : termT} {l : list termT} {b : bool} :
    strongly_normalizing e ->
    (e ->* bool_as_boolT b) ->
    strongly_normalizing (head_appT_list l (iteT (bool_as_boolT b) f g)) ->
    strongly_normalizing (head_appT_list l (iteT e f g)).
Proof.
  move=> Hsn2 Hred1 Hsn1.
  apply (head_appT_strongly_normalizing_gen
    (f := fun f e => match e with exist _ e _ => iteT e f.1 f.2 end)
    (g := fun f _ => iteT (bool_as_boolT b) f.1 f.2)
    (r := relation_restriction (fun e => e ->* bool_as_boolT b) reduction_one)
    (a := (f, g))
    (b := exist _ e Hred1));
    auto using relation_restriction_Acc.
  - move=> i [j Hredj] k Hred2.
    inversion Hred2.
  --- destruct b eqn:Heq.
  ----- right.
        right.
        apply one_reduction_reduction_star.
        eauto using one_reduction.
  ----- fold (bool_as_boolT true) in H0.
        have Habs : bool_as_boolT true = bool_as_boolT false.
  ------- apply normal_form_reduction_star.
  --------- apply normal_form_bool_as_boolT.
  --------- rewrite H0.
            assumption.
  ------- discriminate Habs.
  --- destruct b eqn:Heq.
  ----- fold (bool_as_boolT false) in H0.
        have Habs : bool_as_boolT false = bool_as_boolT true.
  ------- apply normal_form_reduction_star.
  --------- exact normal_form_bool_as_boolT.
  --------- rewrite H0.
            assumption.
  ------- discriminate Habs.
  ----- right.
        right.
        apply one_reduction_reduction_star.
        eauto using one_reduction.
  --- left.
      eexists (exist _ f0 _).
      Unshelve.
      constructor.
  ----- constructor.
        assumption.
  ----- constructor;
        reflexivity.
  ----- eapply normal_form_reduction_star_confluence.
  ------- exact normal_form_bool_as_boolT.
  ------- apply one_reduction_reduction_star.
          exact H3.
  ------- assumption.
  --- right.
      left.
      exists (g0, i.2).
      constructor;
      auto using one_reduction.
  --- right.
      left.
      exists (i.1, h).
      constructor;
      auto using one_reduction.
  - move=> i [j _] k Heq.
    discriminate Heq.
Qed.

Lemma head_appT_list_recT_oT_strongly_normalizing
  {e f : termT} {l : list termT} :
    strongly_normalizing (head_appT_list l e) ->
    strongly_normalizing f ->
    strongly_normalizing (head_appT_list l (recT e f oT)).
Proof.
  move=> Hsn1 Hsn2.
  apply (head_appT_strongly_normalizing_gen
    (f := fun e f => recT e f oT)
    (g := fun e f => e)
    (r := reduction_one));
  auto.
  - move=> a b g Hred.
    inversion Hred.
  --- right.
      right.
      reflexivity.
  --- right.
      left.
      exists f0.
      constructor;
      auto.
  --- left.
      exists g0.
      constructor.
  ----- assumption.
  ----- constructor;
        reflexivity. 
  --- inversion H3.
  - move=> a b c Heq.
    discriminate Heq.
Qed.

Lemma reduction_star_sT_inv {e f : termT} :
    (sT e ->* f) -> exists g : termT, f = sT g.
Proof.
  move=> [n Hred].
  move: e f Hred.
  induction n;
  move=> e f Hred.
  - inversion Hred.
    eauto.
  - inversion Hred.
    inversion H0.
    apply (IHn f1).
    rewrite H6.
    assumption.
Qed.  

Lemma head_appT_list_recT_sT_strongly_normalizing
    {e f g : termT} {l : list termT} :
    strongly_normalizing
      (head_appT_list l (appT (appT f (recT e f g)) g)) ->
    strongly_normalizing (head_appT_list l (recT e f (sT g))).
Proof.
  move=> Hsn.
  apply (
    head_appT_strongly_normalizing_gen
    (f := fun e c => match c with (f, g) => recT e f (sT g) end)
    (g := fun e c => match c with (f, g) => appT (appT f (recT e f g)) g end)
    (r := relation_product reduction_one reduction_one)
    (a := e)
    (b := (f, g))
  ).
  - move=> a [b c] d Hred.
    inversion Hred.
  --- right.
      right.
      reflexivity.
  --- right.
      left.
      exists f0.
      constructor;
      eauto using one_reduction.
  --- left.
      exists (g0, c).
      constructor.
  ----- left.
        assumption.
  ----- constructor.
  ------- reflexivity.
  ------- apply (red_star_next (f := appT (appT g0 (recT a b c)) c)).
  --------- eauto using one_reduction.
  --------- apply one_reduction_reduction_star.
            eauto using one_reduction.
  --- left.
      inversion H3.
      exists (b, f1).
      constructor.
  ----- right.
        assumption.
  ----- constructor.
  ------- reflexivity.
  ------- apply (red_star_next (f := appT (appT b (recT a b f1)) c)).
  --------- eauto using one_reduction.
  --------- apply one_reduction_reduction_star.
            eauto using one_reduction.
  - move=> a [b c] d Heq.
    discriminate Heq.
  - apply relation_product_Acc.
  --- eapply strongly_normalizing_appT_inv_l.
      eapply strongly_normalizing_appT_inv_l.
      eapply head_appT_list_strongly_normalizing_inv.
      exact Hsn.
  --- eapply strongly_normalizing_appT_inv_r.
      eapply head_appT_list_strongly_normalizing_inv.
      exact Hsn.
  - assumption.
Qed. 

Lemma reducibility_candidate_sat_beta_aux {t :  typeT} {e f : termT} {l : list termT} :
    reducibility_candidate t (head_appT_list l (e[O <- f])) ->
    strongly_normalizing f ->
    reducibility_candidate t (head_appT_list l (appT (absT e) f)).
Proof.
  move: e f l.
  induction t;
  move=> e f l Hredu Hsn.
  - destruct Hredu as [Hsn2 [n Hredn]].
    constructor.
    apply head_appT_list_beta_strongly_normalizing;
    try assumption.
    exists n.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - destruct Hredu as [Hsn2 [b Hredb]].
    constructor.
    apply head_appT_list_beta_strongly_normalizing;
    try assumption.
    exists b.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - apply head_appT_list_beta_strongly_normalizing;
    try assumption.
  - move=> g Hredug.
    apply (IHt2 _ _ (cons g l)).
  --- simpl.
      simpl in Hredu.
      apply Hredu.
      assumption.
  --- assumption.
Qed.

Lemma reducibility_candidate_sat_iteT_falseT_aux {t :  typeT} {e f : termT} {l : list termT} :
    reducibility_candidate t (head_appT_list l f) ->
    strongly_normalizing e ->
    reducibility_candidate t (head_appT_list l (iteT falseT e f)).
Proof.
  move: e f l.
  induction t;
  move=> e f l Hredu Hsn.
  - destruct Hredu as [Hsn2 [n Hredn]].
    constructor.
    apply head_appT_list_iteT_falseT_strongly_normalizing;
    try assumption.
    exists n.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - destruct Hredu as [Hsn2 [b Hredb]].
    constructor.
    apply head_appT_list_iteT_falseT_strongly_normalizing;
    try assumption.
    exists b.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - apply head_appT_list_iteT_falseT_strongly_normalizing;
    try assumption.
  - move=> g Hredug.
    apply (IHt2 _ _ (cons g l)).
  --- simpl.
      simpl in Hredu.
      apply Hredu.
      assumption.
  --- assumption.
Qed.

Lemma reducibility_candidate_sat_iteT_trueT_aux
  {t :  typeT} {e f : termT} {l : list termT} :
    reducibility_candidate t (head_appT_list l e) ->
    strongly_normalizing f ->
    reducibility_candidate t (head_appT_list l (iteT trueT e f)).
Proof.
  move: e f l.
  induction t;
  move=> e f l Hredu Hsn.
  - destruct Hredu as [Hsn2 [b Hredb]].
    constructor.
    apply head_appT_list_iteT_trueT_strongly_normalizing;
    try assumption.
    exists b.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - destruct Hredu as [Hsn2 [b Hredb]].
    constructor.
    apply head_appT_list_iteT_trueT_strongly_normalizing;
    try assumption.
    exists b.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - apply head_appT_list_iteT_trueT_strongly_normalizing;
    try assumption.
  - move=> g Hredug.
    apply (IHt2 _ _ (cons g l)).
  --- simpl.
      simpl in Hredu.
      apply Hredu.
      assumption.
  --- assumption.
Qed.

Lemma reducibility_candidate_sat_iteT_aux
  {t :  typeT} {e f g : termT} {l : list termT} {b : bool} :
    strongly_normalizing e ->
    (e ->* bool_as_boolT b) ->
    reducibility_candidate t
      (head_appT_list l (iteT (bool_as_boolT b) f g)) ->
    reducibility_candidate t (head_appT_list l (iteT e f g)).
Proof.
  move: e f g l b.
  induction t;
  move=> e f g l b Hsn Hred Hredu.
  - destruct Hredu as [Hsn2 [n Hredn]].
    constructor.
    apply (head_appT_list_iteT_strongly_normalizing (b := b));
    try assumption.
    exists n.
    transitivity (head_appT_list l (iteT (bool_as_boolT b) f g)).
  --- apply head_appT_list_reduction_star.
      apply reduction_star_iteT;
      try reflexivity.
      assumption.
  --- assumption.
  - destruct Hredu as [Hsn2 [c Hredc]].
    constructor.
    apply (head_appT_list_iteT_strongly_normalizing (b := b));
    try assumption.
    exists c.
    transitivity (head_appT_list l (iteT (bool_as_boolT b) f g)).
  --- apply head_appT_list_reduction_star.
      apply reduction_star_iteT;
      try reflexivity.
      assumption.
  --- assumption.
  - apply (head_appT_list_iteT_strongly_normalizing (b := b));
    try assumption.
  - move=> h Hreduh.
    apply (IHt2 _ _ _ (h :: l)%list b).
  --- assumption.
  --- assumption.
  --- simpl.
    simpl in Hredu.
    apply Hredu.
    assumption. 
Qed.

Lemma reducibility_candidate_sat_recT_oT_aux
  {t :  typeT} {e f : termT} {l : list termT} :
    reducibility_candidate t (head_appT_list l e) ->
    strongly_normalizing f ->
    reducibility_candidate t (head_appT_list l (recT e f oT)).
Proof.
  move: e f l.
  induction t;
  move=> e f l Hredu Hsn.
  - destruct Hredu as [Hsn2 [n Hredn]].
    constructor.
    apply head_appT_list_recT_oT_strongly_normalizing;
    try assumption.
    exists n.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - destruct Hredu as [Hsn2 [n Hredn]].
    constructor.
    apply head_appT_list_recT_oT_strongly_normalizing;
    try assumption.
    exists n.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - apply head_appT_list_recT_oT_strongly_normalizing;
    try assumption.
  - move=> g Hredug.
    apply (IHt2 _ _ (cons g l)).
  --- simpl.
      simpl in Hredu.
      apply Hredu.
      assumption.
  --- assumption.
Qed.

Lemma reducibility_candidate_sat_recT_sT_aux
  {t :  typeT} {e f g : termT} {l : list termT} :
    reducibility_candidate t
      (head_appT_list l (appT (appT f (recT e f g)) g)) ->
    reducibility_candidate t
      (head_appT_list l (recT e f (sT g))).
Proof.
  move: e f g l.
  induction t;
  move=> e f g l Hredu.
  - destruct Hredu as [Hsn2 [n Hredn]].
    constructor.
    apply head_appT_list_recT_sT_strongly_normalizing;
    try assumption.
    exists n.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - destruct Hredu as [Hsn2 [n Hredn]].
    constructor.
    apply head_appT_list_recT_sT_strongly_normalizing;
    try assumption.
    exists n.
    eapply red_star_next.
  --- eauto using head_appT_list_one_reduction, one_reduction.
  --- assumption.
  - apply head_appT_list_recT_sT_strongly_normalizing;
    try assumption.
  - move=> h Hreduh.
    apply (IHt2 _ _ _ (h :: l)%list).
  --- simpl.
      simpl in Hredu.
      apply Hredu.
      assumption.
Qed.

Lemma reducibility_candidate_sat_beta {t :  typeT} {e f : termT} :
    reducibility_candidate t (e[O <- f]) ->
    strongly_normalizing f ->
    reducibility_candidate t (appT (absT e) f).
Proof.
  exact (
    reducibility_candidate_sat_beta_aux
      (t := t) (e := e) (f := f) (l := nil)
  ).
Qed.

Lemma reducibility_candidate_strongly_normalizing_aux {t : typeT} :
    (exists e : termT, reducibility_candidate t e /\ bound_closed e) /\
    (forall e : termT, reducibility_candidate t e -> strongly_normalizing e).
Proof.
  induction t;
    simpl.
  - constructor.
  --- exists (nat_as_natT O).
      (* With how things are defined, it is slighty easier to write
         [nat_as_natT O] instead of [oT]. *)
      constructor.
  ----- constructor.
  ------- apply normal_form_strongly_normalizing.
          exact normal_form_nat_as_natT.
  ------- exists O.
          reflexivity.
  ----- apply bound_closed_nat_as_natT.
  --- move=> e [Hsn _].
      assumption.
  - constructor.
  --- exists (bool_as_boolT false).
      constructor.
  ----- constructor.
  ------- apply normal_form_strongly_normalizing.
          exact normal_form_bool_as_boolT.
  ------- exists false.
          reflexivity.
  ----- apply bound_closed_bool_as_boolT. 
  --- move=> e [Hsn _].
      assumption.
  - constructor.
  --- exists (fvarT default_fident).
      constructor.
  ----- apply normal_form_strongly_normalizing.
        exact normal_form_fvarT.
  ----- unfold bound_closed.
        auto using bound_nclosed. 
  --- auto.
  - destruct IHt1 as [[e [Hredue Hbnde]] Hsne].
    destruct IHt2 as [[f [Hreduf Hbndf]] Hsnf].
    constructor.
  --- exists (absT f).
      constructor.
  ----- move=> g Hredug.
        apply reducibility_candidate_sat_beta.
  ------- rewrite (bound_closed_bsubst Hbndf).
          assumption.
  ------- auto.
  ----- unfold bound_closed.
        eauto using bound_nclosed, bound_closed_bound_nclosed.
  --- move=> g Hacc.
      eapply strongly_normalizing_appT_inv_l.
      apply Hsnf.
      apply Hacc.
      exact Hredue.
Qed.

Lemma reducibility_candidate_strongly_normalizing {t : typeT} {e : termT} :
    reducibility_candidate t e -> strongly_normalizing e.
Proof.
  move: e.
  exact reducibility_candidate_strongly_normalizing_aux.2.
Qed.

Lemma reducibility_candidate_sat_iteT_falseT {t : typeT} {e f : termT} :
    reducibility_candidate t f ->
    strongly_normalizing e ->
    reducibility_candidate t (iteT falseT e f).
Proof.
  exact (
    reducibility_candidate_sat_iteT_falseT_aux
      (t := t) (e := e) (f := f) (l := nil)
  ).
Qed.

Lemma reducibility_candidate_sat_iteT_trueT {t : typeT} {e f : termT} :
    reducibility_candidate t e ->
    strongly_normalizing f ->
    reducibility_candidate t (iteT trueT e f).
Proof.
  exact (
    reducibility_candidate_sat_iteT_trueT_aux
      (t := t) (e := e) (f := f) (l := nil)
  ).
Qed.

Lemma reducibility_candidate_sat_recT_oT {t : typeT} {e f : termT} :
    reducibility_candidate t e ->
    strongly_normalizing f ->
    reducibility_candidate t (recT e f oT).
Proof.
  exact (
    reducibility_candidate_sat_recT_oT_aux
      (t := t) (e := e) (f := f) (l := nil)
  ).
Qed.

Lemma reducibility_candidate_sat_recT_sT {t : typeT} {e f g : termT} :
    reducibility_candidate t (appT (appT f (recT e f g)) g) ->
    reducibility_candidate t (recT e f (sT g)).
Proof.
exact (
    reducibility_candidate_sat_recT_sT_aux
      (t := t) (e := e) (f := f) (l := nil)
  ).
Qed.

Lemma reducibility_candidate_sat_recT {t : typeT} {e f g : termT} {n : nat} :
    strongly_normalizing g ->
    reducibility_candidate (t ->T natT ->T t) f ->
    (g ->* nat_as_natT n) ->
    reducibility_candidate t (recT e f (nat_as_natT n)) ->
    reducibility_candidate t (recT e f g).
Proof.
  move: e f g.
  induction n;
  move=> e f g Hsn Hredue Hreduf Hred Hredu.
  - simpl.
    simpl in Hredu.
    induction Hsn.
    move: Hredu.
    generalize (eq_refl (recT e f oT)).
    generalize (recT e f oT) at -2.
    move=> g Heq Hredug.
    have Hsn2 := reducibility_candidate_strongly_normalizing Hredug.
    induction Hsn2.
    apply TODO.
  -    

Lemma reducibility_candidate_sat_iteT {t : typeT} {e f g : termT} {b : bool} :
    strongly_normalizing e ->
    (e ->* bool_as_boolT b) ->
    reducibility_candidate t (iteT (bool_as_boolT b) f g) ->
    reducibility_candidate t (iteT e f g).
Proof.
  exact (
    reducibility_candidate_sat_iteT_aux
      (t := t) (e := e) (f := f) (g := g) (b := b) (l := nil)
  ).
Qed.

Lemma reducibility_candidate_par_bsubst_derivation
  {t : typeT} {e : termT} {G : Context.t} {s : NatMap.t termT} :
    FMap.Empty (Context.fmap G) ->
    (forall (n : nat) (t : typeT), Context.bMapsTo n t G ->
      exists e : termT,
      NatMap.MapsTo n e s /\ reducibility_candidate t e) ->
    G |- e :T t -> reducibility_candidate t (par_bsubst s e).
Proof.
  move=> Hem Hmap Hderiv.
  move: s Hem Hmap.
  induction Hderiv;
  move=> s Hem Hmap;
  simpl.
  - have [e [Hmaps Hredu]] := Hmap _ _ H.
    apply NatMap.find_1 in Hmaps.
    rewrite Hmaps.
    assumption.
  - destruct (Hem _ _ H).
  - move=> f Hredu.
    apply reducibility_candidate_sat_beta.
  --- apply TODO.
  --- eapply reducibility_candidate_strongly_normalizing.
      exact Hredu.
  - apply IHHderiv1;
    try assumption.
    fold reducibility_candidate.
    apply IHHderiv2;
    assumption.
  - constructor.
  --- apply normal_form_strongly_normalizing.
      apply (@normal_form_bool_as_boolT true). 
  --- exists true;
      reflexivity.
  - constructor.
  --- apply normal_form_strongly_normalizing.
      apply (@normal_form_bool_as_boolT false). 
  --- exists false;
      reflexivity.
  - destruct (IHHderiv1 s Hem Hmap) as [Hsn [b Hred]].
    apply (reducibility_candidate_sat_iteT (b := b)); 
    auto.
    destruct b.
  --- apply reducibility_candidate_sat_iteT_trueT;
      eauto using reducibility_candidate_strongly_normalizing.
  --- apply reducibility_candidate_sat_iteT_falseT;
      eauto using reducibility_candidate_strongly_normalizing.
  - constructor.
  --- apply normal_form_strongly_normalizing.
      apply (@normal_form_nat_as_natT O). 
  --- exists O;
      reflexivity.
  - constructor.
  --- apply strongly_normalizing_f.
  ----- move=> f g Hred.
        inversion Hred.
        assumption.
  ----- move=> f g Hred.
        inversion Hred.
        eauto.
  ----- apply IHHderiv;
        assumption.
  --- have [_ [n Hred]] := IHHderiv s Hem Hmap.
      exists (S n).
      simpl.
      apply reduction_star_sT.
      assumption.
  - have [_ [n Hred]] := IHHderiv3 s Hem Hmap.
    apply (reducibility_candidate_sat_recT (n := n));
    eauto using reducibility_candidate_strongly_normalizing.
    clear g Hred Hderiv3 IHHderiv3.
    induction n.
  --- simpl.
      apply (reducibility_candidate_sat_recT_oT);
      eauto using reducibility_candidate_strongly_normalizing.
  --- simpl.
      apply (reducibility_candidate_sat_recT_sT).
      apply IHHderiv2;
      auto.
      constructor.
  ----- apply normal_form_strongly_normalizing.
        exact normal_form_nat_as_natT.
  ----- exists n.
        reflexivity.  
Qed.

Lemma reducibility_candidate_empty_derivation {t : typeT} {e : termT} :
    |- e :T t -> reducibility_candidate t e.
Proof.
  move=> Hderiv.
  rewrite <- (par_bsubst_empty (s := NatMap.empty termT)).
  - apply (reducibility_candidate_par_bsubst_derivation (G := Context.empty)).
  --- apply (FMap.empty_1).
  --- move=> n u Hmap.
      unfold Context.bMapsTo in Hmap.
      simpl in Hmap.
      destruct n;
      simpl in Hmap;
      discriminate Hmap.
  --- exact Hderiv.
  - exact (@NatMap.empty_1 termT).
Qed.  

Fixpoint iter_absT (n : nat) (e : termT) :=
  match n with
  | O => e
  | S n => absT (iter_absT n e)
  end.

Lemma iter_absT_absT {n : nat} (e : termT) :
    iter_absT n (absT e) = absT (iter_absT n e).
Proof.
  induction n;
  simpl;
  try rewrite IHn;
  reflexivity.
Qed.

Lemma strongly_normalizing_iter_absT_inv {n : nat} {e : termT} :
    strongly_normalizing (iter_absT n e) -> strongly_normalizing e.
Proof.
  move: e.
  induction n;
  auto;
  simpl.
  move=> e Hsn.
  apply IHn.
  apply strongly_normalizing_absT_inv.
  assumption.
Qed.

Lemma derivation_iter_absT {n : nat} {e : termT} {t : typeT} {G : Context.t} :
    n = length (Context.bmap G) ->
    G |- e :T t -> exists u : typeT,
    {| Context.bmap := nil; Context.fmap := Context.fmap G |} |-
      iter_absT n e :T u.
Proof.
  move: e t G.
  induction n;
  move=> e t G Hlen Hderiv;
  destruct G;
  simpl in Hlen;
  simpl.
  - apply eq_sym in Hlen.
    rewrite List.length_zero_iff_nil in Hlen.
    rewrite Hlen in Hderiv.
    eauto.
  - destruct bmap.
  --- discriminate Hlen.
  --- rewrite <- iter_absT_absT.
      have Hderiv2 := IHn (absT e) (t0 ->T t)
        {| Context.bmap := bmap; Context.fmap := fmap |}.
      simpl in Hderiv2.
      apply Hderiv2.
  ----- simpl in Hlen.
        inversion Hlen.
        reflexivity.
  ----- eauto using derivation.
Qed.

Lemma fclosed_derivation_strongly_normalizing
  {e : termT} {t : typeT} {G : Context.t} :
  Context.fmap G = FMap.empty typeT -> G |- e :T t ->
  strongly_normalizing e.
Proof.
  move=> Hem Hderiv.
  apply (strongly_normalizing_iter_absT_inv (n := length (Context.bmap G))).
  destruct (derivation_iter_absT
    (n := length (Context.bmap G))
    (e := e)
    (t := t)
    (G := G));
  auto.
  rewrite Hem in H.
  fold Context.empty in H.
  apply (reducibility_candidate_strongly_normalizing (t := x)).
  apply reducibility_candidate_empty_derivation.
  apply H.
Qed.

Fixpoint index (l : list fident) (x : fident) :=
    match l with
    | nil => O
    | cons y l =>
      match FIdentFacts.eqb x y with
      | true => O
      | false => S (index l x)
      end
    end.

#[export] Instance Proper_index : Morphisms.Proper (SetoidList.eqlistA FIdentFacts.eq ==> FIdentFacts.eq ==> eq) index.
Proof.
  move=> l m Heq1 x y Heq2.
  induction Heq1.
  - reflexivity.
  - simpl.
    destruct (FIdentFacts.eqb x x0) eqn:Heq3;
    move/ FIdentFacts.eqb_spec in Heq3;
    rewrite Heq2 in Heq3;
    rewrite H in Heq3;
    move/ FIdentFacts.eqb_spec in Heq3.
  --- rewrite Heq3.
      reflexivity.
  --- unfold "~~" in Heq3.
      inversion Heq3.
      destruct (FIdentFacts.eqb y x') eqn:Heq4;
      try discriminate H1.
      f_equal.
      exact IHHeq1.
Qed.

Lemma eliminate_fvarT_derivation
  {e : termT} {t : typeT} {G : Context.t} :
    G |- e :T t ->
    exists (s : FMap.t termT) (l : list typeT), {|
      Context.bmap := (Context.bmap G) ++ l;
      Context.fmap := FMap.empty typeT
    |} |- par_fsubst s e :T t.
Proof.
  simpl.
  move=> Hderiv.
  pose elements := FMap.elements (Context.fmap G).
  exists
    (FMap.mapi
      (fun x _ =>
        bvarT
          (index
            (List.map
              (fun c : fident * typeT =>
                let (x, _) := c in x)
              elements)
            x +
            length (Context.bmap G)))
        (Context.fmap G)).
  exists
    (List.map
      (fun c : fident * typeT =>
        let (_, x) := c in x)
      elements).
  induction Hderiv;
  simpl;
  eauto using derivation.
  - apply bvarT_ax.
    unfold Context.bMapsTo.
    simpl.
    rewrite List.nth_error_app1.
    unfold Context.bMapsTo in H.
  --- apply (List.nth_error_Some _ _).1.
      move=> Heq.
      rewrite Heq in H.
      discriminate H.
  --- assumption.
  - rewrite FMapFacts.mapi_o.
  --- move=> y z _ Heq.
      rewrite Heq.
      reflexivity.
  --- unfold Context.fMapsTo in H.
      rewrite FMapFacts.find_mapsto_iff in H.
      rewrite H.
      simpl.
      apply bvarT_ax.
      unfold Context.bMapsTo.
      simpl.
      rewrite List.nth_error_app2.
      Lia.lia.
      rewrite Nat.add_sub.
      apply FMap.find_2 in H.
      apply FMap.elements_1 in H.
      have bar := (FMap.elements_3w (Context.fmap G)).
      induction H.
  ----- destruct y as [y u].
        unfold elements.
        simpl.
        unfold FMap.eq_key_elt in H.
        simpl in H.
        destruct H as [Heq1 Heq2].
        move/ FIdentFacts.eqb_spec in Heq1.
        rewrite Heq1.
        simpl.
        rewrite Heq2.
        reflexivity.
  ----- inversion bar.
        destruct y as [y u].
        simpl.
        destruct (FIdentFacts.eqb x y) eqn:Heq2.
  ------- move/ FIdentFacts.eqb_spec in Heq2.
          destruct H2.
          eapply (SetoidList.InA_eqA _ (x := (x, t))).
          Unshelve.
  --------- unfold FMap.eq_key.
              simpl.
              exact Heq2.
  --------- clear IHInA bar H3 H1.
            induction H.
  ----------- destruct y0 as [z v].
              unfold FMap.eq_key_elt in H.
              destruct H as [Heq3 _].
              apply SetoidList.InA_cons_hd.
              unfold FMap.eq_key.
              assumption.
  ----------- apply SetoidList.InA_cons_tl.
              assumption.
  --------- constructor.
  ----------- move=> [z v].
              unfold FMap.eq_key.
              reflexivity.
  ----------- move=> [z v] [z' v'].
              unfold FMap.eq_key.
              simpl.
              move=> Heq5.
              rewrite Heq5.
              reflexivity.
  ----------- move=> [z v] [z' v'] [z'' v''].
              unfold FMap.eq_key.
              simpl.
              move=> Heq5 Heq6.
              transitivity z';
              eauto.
  ------- simpl.
          apply IHInA.
          assumption.
  - apply absT_in.
    unfold Context.bpush.
    simpl.
    unfold Context.bpush in IHHderiv.
    simpl in IHHderiv.
    have foo : FMap.Equal
      (FMap.mapi
        (fun x : FIdent.t =>
          fun=> bvarT
            (index
              (List.map (fun c : fident * typeT =>
                let (x0, _) := c in x0)
                elements) x +
                S (length (Context.bmap G)))) (Context.fmap G))
      (FMap.map (bshift 0)
        (FMap.mapi
          (fun x : FIdent.t =>
            fun=> bvarT
              (index
                (List.map (fun c : fident * typeT =>
                  let (x0, _) := c in x0)
                  elements) x +
                  length (Context.bmap G))) (Context.fmap G))).
  --- move=> z.
      rewrite FMapFacts.map_o.
      repeat rewrite FMapFacts.mapi_o;
      try (
        move=> x y _ Heq;
        rewrite Heq;
        reflexivity
      ).
      destruct (FMap.find z (Context.fmap G));
      simpl;
      try reflexivity.
      repeat f_equal.
      Lia.lia.
  --- rewrite <- foo.
      assumption.
Qed. 

Theorem derivation_strongly_normalizing
  {e : termT} {t : typeT} {G : Context.t} :
    G |- e :T t -> strongly_normalizing e.
Proof.
  move=> Hderiv.
  destruct (eliminate_fvarT_derivation Hderiv) as [s [l Hderiv2]].
  apply (strongly_normalizing_par_fsubst_inv (s := s)).
  apply (fclosed_derivation_strongly_normalizing
    (G := {|
      Context.bmap := Context.bmap G ++ l;
      Context.fmap := FMap.empty typeT
    |})
    (t := t));
  auto.
Qed.