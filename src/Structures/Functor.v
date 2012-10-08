Class Functor T := { fmap : forall {A B}, (A -> B) -> T A -> T B}.

Module FunctorNotation.
  Infix "<$>" := fmap (at level 45, right associativity).
End FunctorNotation.