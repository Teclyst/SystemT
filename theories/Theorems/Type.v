Require Import Definitions.Type.

Require Import ssreflect ssrfun ssrbool.

Lemma par_tsubst_empty {s : TMap.t typeT} {t : typeT} :
    TMap.Empty s -> par_tsubst s t = t.
Proof.
  move=> Hem.
  induction t;
  simpl;
  f_equal;
  auto.
  destruct (TMap.find k s) eqn:Heq;
  try reflexivity.
  destruct (Hem k t).
  apply TMap.find_2.
  assumption.
Qed.

Definition tsubst_compose (s h : TMap.t typeT) :=
  TMap.map2
    (fun opt1 opt2 =>
      match opt1, opt2 with
      | Some t, _ => Some (par_tsubst h t)
      | _, Some t => Some t
      | _, _ => None end)
    s h.

Lemma par_tsubst_par_tsubst {s h : TMap.t typeT} {t : typeT} :
    par_tsubst h (par_tsubst s t) =
    par_tsubst (tsubst_compose s h) t.
Proof.
  induction t;
  simpl;
  f_equal;
  eauto.
  unfold tsubst_compose.
  rewrite TMapFacts.map2_1bis;
  destruct (TMap.find k s);
  simpl;
  destruct (TMap.find k h);
  reflexivity.
Qed.
