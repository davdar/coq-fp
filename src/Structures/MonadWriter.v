Require Import Data.Prod.

Class Writer w (m:Type -> Type) :=
{ tell : w -> m unit
; listen : forall {A}, m A -> m (A*w)
; pass : forall {A}, m (A*(w -> w)) -> m A
}.
