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

Lemma strongly_normalizing_absT_inv {e : termT} :
    strongly_normalizing (absT e) ->
    strongly_normalizing e.
Proof.
  generalize (eq_refl (absT e)).
  pattern (absT e) at -1.
  generalize (absT e) at -2.
  simpl.
  move=> f Heq Hsn.
  rewrite <- Heq in Hsn.
  move: Heq.
  move: e.
  induction Hsn;
  move=> e Heq.
  constructor.
  move=> h Hred.
  eapply (H0 (absT h)).
  - rewrite Heq.
    unfold "1<-" in Hred.
    unfold "1<-".
    eauto using one_reduction.
  - reflexivity.
Qed.

Lemma strongly_normalizing_appT_inv_l {e f : termT} :
    strongly_normalizing (appT e f) ->
    strongly_normalizing e.
Proof.
  generalize (eq_refl (appT e f)).
  pattern (appT e f) at -1.
  generalize (appT e f) at -2.
  simpl.
  move=> g Heq Hsn.
  rewrite <- Heq in Hsn.
  move: Heq.
  move: e f.
  induction Hsn;
  move=> e f Heq.
  constructor.
  move=> h Hred.
  eapply (H0 (appT h f)).
  - rewrite Heq.
    unfold "1<-" in Hred.
    unfold "1<-".
    eauto using one_reduction.
  - reflexivity.
Qed.

Lemma strongly_normalizing_appT_inv_r {e f : termT} :
    strongly_normalizing (appT e f) ->
    strongly_normalizing f.
Proof.
  generalize (eq_refl (appT e f)).
  pattern (appT e f) at -1.
  generalize (appT e f) at -2.
  simpl.
  move=> g Heq Hsn.
  rewrite <- Heq in Hsn.
  move: Heq.
  move: e f.
  induction Hsn;
  move=> e f Heq.
  constructor.
  move=> h Hred.
  eapply (H0 (appT e h)).
  - rewrite Heq.
    unfold "1<-" in Hred.
    unfold "1<-".
    eauto using one_reduction.
  - reflexivity.
Qed.

Lemma strongly_normalizing_bsubst_inv {e f : termT} {n : nat} :
    strongly_normalizing (e[n <- f]) ->
    strongly_normalizing e.
Proof.
  generalize (eq_refl (e[n <- f])).
  pattern (e[n <- f]) at -1.
  generalize (e[n <- f]) at -2.
  simpl.
  move=> g Heq Hsn.
  rewrite <- Heq in Hsn.
  move: Heq.
  move: e f.
  induction Hsn;
  move=> e f Heq.
  constructor.
  move=> h Hred.
  eapply (H0 (h[n <- f])).
  - rewrite Heq.
    unfold "1<-" in Hred.
    unfold "1<-".
    eauto using one_reduction_bsubst_l.
  - reflexivity.
Qed.

Lemma strongly_normalizing_par_fsubst_inv {e : termT} {s : FMap.t termT} :
    strongly_normalizing (par_fsubst s e) ->
    strongly_normalizing e.
Proof.
  generalize (eq_refl (par_fsubst s e)).
  pattern (par_fsubst s e) at -1.
  generalize (par_fsubst s e) at -2.
  simpl.
  move=> g Heq Hsn.
  rewrite <- Heq in Hsn.
  move: Heq.
  move: e.
  induction Hsn;
  move=> e Heq.
  constructor.
  move=> h Hred.
  eapply (H0 (par_fsubst s h)).
  - rewrite Heq.
    unfold "1<-" in Hred.
    unfold "1<-".
    eauto using one_reduction_par_fsubst.
  - reflexivity. 
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

Fixpoint head_appT_list (e : termT) (l : list termT) : termT :=
  match l with
  | nil => e
  | cons f l => appT (head_appT_list e l) f
  end.

Lemma reducibility_candidate_sat_beta_aux {t :  typeT} {e f : termT} {l : list termT} :
    reducibility_candidate t (head_appT_list (e[O <- f]) l) ->
    strongly_normalizing f ->
    reducibility_candidate t (head_appT_list (appT (absT e) f) l).
Proof.
Admitted.

Lemma reducibility_candidate_sat_beta {t :  typeT} {e f : termT} :
    reducibility_candidate t (e[O <- f]) ->
    strongly_normalizing f ->
    reducibility_candidate t (appT (absT e) f).
Proof.
  exact (reducibility_candidate_sat_beta_aux (t := t) (e := e) (f := f) (l := nil)).
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

Lemma reducibility_candidate_par_bsubst_derivation
  {t : typeT} {e : termT} {G : Context.t} {s : NatMap.t termT} :
    FMap.Empty (Context.fmap G) ->
    (forall (n : nat) (t : typeT), Context.bMapsTo n t G ->
      exists e : termT,
      NatMap.MapsTo n e s /\ reducibility_candidate t e) ->
    G |- e :T t -> reducibility_candidate t (par_bsubst s e).
Admitted.

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