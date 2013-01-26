Require Import FP.Data.Function.
Require Import FP.Relations.Setoid.

Import FunctionNotation.

Definition rel A := A -> A -> Prop.

Definition mor_resp {A B:Type}
    (PRel:rel Prop) (R1:rel A) (R2:rel B) : rel (A -> B) :=
  fun f g => forall x y, PRel (R1 x y) (R2 (f x) (g y)).
Arguments mor_resp {A B} / _ _ _ _ _.

Definition mor_resp_impl {A B}
  : rel A -> rel B -> rel (A -> B) := mor_resp impl.
Arguments mor_resp_impl {A B} / _ _ _ _.
Arguments respectful {A B} / _ _ _ _.
Definition mor_resp_follows {A B}
  : rel A -> rel B -> rel (A -> B) := mor_resp follows.
Arguments mor_resp_follows {A B} / _ _ _ _.
Definition mor_resp_iff {A B}
  : rel A -> rel B -> rel (A -> B) := mor_resp iff.
Arguments mor_resp_iff {A B} / _ _ _ _.

Module MorphismNotation.
  (*
  Infix "==>" := mor_resp_impl (at level 55, right associativity).
*)
  Open Scope signature_scope.
  Infix "<==" := mor_resp_follows (at level 55, right associativity).
  Infix "<==>" := mor_resp_iff (at level 55, right associativity).
End MorphismNotation.