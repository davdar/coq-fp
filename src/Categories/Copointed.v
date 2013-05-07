Require Import FP.CoreClasses.

Class Counit t := { counit : forall {A}, t A -> A }.

Section CopointedWF.
  Context {t} `{! Counit t ,! F_Eqv t ,! F_PER_WF t }.
  Class CopointedWF :=
    { Pointed_InjectionRespect :
        forall {A} `{! Eqv A ,! PER_WF A },
        InjectionRespect (t A) A counit eqv eqv
    }.
End CopointedWF.