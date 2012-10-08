Class MonadFail e (m:Type -> Type) :=
{ throw : forall {A}, e -> m A
; catch : forall {A}, m A -> (e -> m A) -> m A
}.
