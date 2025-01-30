Require Import ExtrOcamlString.

From SystemT Require Import Definitions.Term.
From SystemT Require Import Theorems.Reduction.
From SystemT Require Import Theorems.TermExample.

Require Extraction.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive option_eq => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "coqInterpreter" FMap termT nat_as_natT addT reduce par_fsubst.