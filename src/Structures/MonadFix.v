Class MonadFix m :=
{ mfix : forall {A B:Type}, ((A -> m B) -> (A -> m B)) -> (A -> m B) }.