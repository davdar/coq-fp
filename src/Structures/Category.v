Class Category (t:Type -> Type -> Type) :=
  { ccompose : forall {A B C}, t B C -> t A B -> t A C }.

Module CategoryNotation.
  Infix "<.>" := ccompose (at level 45, right associativity).
End CategoryNotation.