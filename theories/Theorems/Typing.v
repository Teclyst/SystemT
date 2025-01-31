Require Import Definitions.Ident.
Require Import Definitions.Type.
Require Import Definitions.Term.
Require Import Definitions.Typing.
Require Import Definitions.Context.
Require Import Theorems.Context.
Require Import Theorems.Type.

Require Import ssreflect ssrfun ssrbool.

Open Scope system_t_type_scope.
Open Scope system_t_term_scope.

Lemma derivation_context_order_with_tsubst
  {G H : Context.t} {e : termT} {t : typeT} {s : TMap.t typeT} :
    G >><c(s) H -> G |- e :T t -> H |- e :T t >> s.
Proof.
  move=> [Hbmap Hfmap] D.
  move: H Hbmap Hfmap.
  induction D;
  eauto using derivation;
  simpl.
  - move=> I Hbmap Hfmap.
    rewrite par_tsubst_par_tsubst.
    apply fvarT_ax.
    auto.
  - move=> H Hbmap Hfmap.
    apply absT_in.
    have Htsubst : G >><c(s) H.
    constructor;
    auto.
    rewrite (context_order_with_tsubst_bpush (t := t)) in Htsubst.
    destruct Htsubst as [Hbmap2 Hfmap2].
    apply IHD;
    assumption.
Qed.

Lemma derivation_no_context_derivation
  {G : Context.t} {e : termT} {t : typeT} :
    |- e :T t -> G |- e :T t.
Proof.
  rewrite <- (par_tsubst_empty (@TMap.empty_1 _)) at -1.
  apply derivation_context_order_with_tsubst.
  exact empty_context_order_with_tsubst.
Qed.
