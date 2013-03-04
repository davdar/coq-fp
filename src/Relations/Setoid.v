Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.RelationClasses.

Require Import FP.Data.Function.

Import FunctionNotation.

Definition inverse_respectful {A B} (R1:relation A) (R2:relation B) : relation (A -> B) :=
  fun f g =>
    forall x y,
      f x `R2` g y -> x `R1` y.

Module ProperNotation.
  Notation "R1 ++> R2" := (respectful R1 R2) (right associativity, at level 55).
  Notation "R1 ==> R2" := (respectful R1 R2) (right associativity, at level 55).
  Notation "R1 --> R2" := (respectful (inverse R1) R2) (right associativity, at level 55).
  Notation "R1 <== R2" := (inverse_respectful R1 R2) (right associativity, at level 55).
End ProperNotation.
