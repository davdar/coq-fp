Require Import FP.CoreClasses.

Class FUnit t := { funit : forall {A}, A -> t A }.

Section PointedWF.
  Context {t} `{! FUnit t ,! F_Eqv t ,! F_PER_WF t }.
  Class PointedWF :=
    { Pointed_InjectionRespect :>
        forall {A} `{! Eqv A ,! PER_WF A },
        InjectionRespect A (t A) funit eqv eqv
    }.

  Context `{! PointedWF }.
End PointedWF.
Arguments PointedWF t {_ _}.
Hint Extern 9 (Proper eqv funit) => apply Proper_inj : typeclass_instances.