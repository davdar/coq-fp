Require Import FP.CoreClasses.
Require Import FP.CoreData.

Import CoreDataNotation.

Class Pointed t := { point : forall {A}, A -> t A }.

Section PointedWF.
  Context {t} `{! Pointed t ,! F_Eqv t ,! F_PER_WF t }.
  Class PointedWF :=
    { point_Proper :> forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv point
    }.
End PointedWF.
Arguments PointedWF t {_ _}.
Hint Extern 9 (Proper eqv (point (t:=?t) (A:=?A))) =>
  let H := fresh "H" in
  pose (H:=(point_Proper (t:=t) (A:=A))) ; apply H
  : typeclass_instances.