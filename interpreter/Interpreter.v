Require Import ExtrOcamlString.

From SystemT Require Import Definitions.Term.
From SystemT Require Import Theorems.Reduction.

Require Extraction.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive option_eq => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "coqInterpreter" termT reduce.