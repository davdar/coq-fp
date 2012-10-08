Class MonadState s m :=
{ get : m s
; put : s -> m unit
}.
