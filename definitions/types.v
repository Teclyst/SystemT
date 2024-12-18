Declare Scope system_t_type_scope.

Inductive TypeT :=
  | natT : TypeT
  | boolT : TypeT
  | tT : nat -> TypeT
  | funT : TypeT -> TypeT -> TypeT.

Notation "t ->T u" := (funT t u) (at level 80, right associativity).