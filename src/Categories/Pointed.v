Require Import FP.CoreClasses.

Class FUnit t := { funit : forall {A}, A -> t A }.

Section PointedWF.
  Context {t} `{! FUnit t ,! F_Eqv t ,! F_PER_WF t }.
  Class PointedWF :=
    { Pointed_Proper :> forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv funit
    }.
End PointedWF.
Arguments PointedWF t {_ _}.
Hint Extern 9 (Proper eqv (funit (t:=?t) (A:=?A))) =>
  let H := fresh "H" in
  pose (H:=(Pointed_Proper (t:=t) (A:=A))) ; apply H
  : typeclass_instances.