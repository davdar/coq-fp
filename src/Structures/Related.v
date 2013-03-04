Require Import FP.Relations.Setoid.

Import ProperNotation.


Definition rel (T:Type) := T -> T -> Prop.

Section morph_proper.
  Context {T:Type}.
  Context {x:T} {y:T}.
  Context {R:T -> T -> Prop} {RWF:PER R}.
  Variable (fP:R x y).
  Definition morph_proper_left : Proper R x.
  Proof.
    unfold Proper.
    transitivity y ; auto.
    symmetry ; auto.
  Qed.
  Definition morph_proper_right : Proper R y.
  Proof.
    unfold Proper.
    transitivity x ; auto.
    symmetry ; auto.
  Qed.
End morph_proper.
