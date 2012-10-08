Class MonadReader e m :=
{ ask : m e
; local : forall {A}, (e -> e) -> m A -> m A
}.
