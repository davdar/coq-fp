Class MonadDelay (m:Type -> Type) :=
  { force : forall {A}, m A -> m A }.