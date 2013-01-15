Require Import FP.Data.Function.

Import FunctionNotation.

Definition fun_respect {A} {B}
    (r1:A -> A -> Prop) (r2:B -> B -> Prop)
    (f1:A -> B) (f2:A -> B) : Prop :=
  forall (a1:A) (a2:A), r1 a1 a2 -> r2 (f1 a1) (f2 a2).

Module RespectNotation.
  Infix "==>" := fun_respect (at level 55, right associativity).
End RespectNotation.
  
           