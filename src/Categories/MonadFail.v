Class MTry (m:Type->Type) :=
  { mtry : forall {A}, m A -> m A -> m A }.

Module MonadFailNotation.
  Infix "<|>" := mtry (at level 48, left associativity).
End MonadFailNotation.