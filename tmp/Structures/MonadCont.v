Class MonadCont R m :=
  { callcc : forall {A}, ((A -> m R) -> m R) -> m A }.