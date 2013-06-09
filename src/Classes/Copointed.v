Require Import FP.CoreClasses.

Class Copointed t := { copoint : forall {A}, t A -> A }.
Arguments copoint {t Copointed A} _ : simpl never.

Section CopointedWF.
  Context {t} `{! Copointed t ,! F_Eqv t ,! F_PER_WF t }.
  Class CopointedWF :=
    { copoint_Proper :>
        forall {A} `{! Eqv A ,! PER_WF A },
        Proper eqv (copoint (A:=A))
    }.
End CopointedWF.