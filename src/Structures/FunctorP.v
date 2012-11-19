Class FunctorP (P:Type -> Type) t :=
  { fmap_p : forall {A B} {p:P B}, (A -> B) -> t A -> t B }.
