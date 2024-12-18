Declare Scope system_t_term_scope.

Inductive termT :=
  | xT : nat -> termT
  | absT : termT -> termT
  | appT : termT -> termT -> termT
  | oT : termT
  | sT : termT -> termT
  | trueT : termT
  | falseT : termT
  | iteT : termT -> termT -> termT -> termT
  | recT : termT -> termT -> termT -> termT.