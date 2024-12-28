Declare Scope system_t_type_scope.

Inductive typeT :=
  | natT : typeT
  | boolT : typeT
  | tT : nat -> typeT
  | funT : typeT -> typeT -> typeT.

Notation "t ->T u" := (funT t u) (at level 80, right associativity).