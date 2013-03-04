Require Import FP.Structures.FZero.

Class FTry (t:Type -> Type) : Type :=
  { try : forall {A}, t A -> t A -> t A }.

Class Failable (t:Type -> Type) : Type :=
  { Failable_FZero : FZero t
  ; Failable_FTry : FTry t
  }.
Hint Resolve Build_Failable : typeclass_instances.
Hint Immediate Failable_FZero : typeclass_instances.
Hint Immediate Failable_FTry : typeclass_instances.

Section Failable.
  Context {t} {FZero_:FZero t} {Failable_:Failable t}.
  
  Definition fail {A} : t A := fzero.
End Failable.