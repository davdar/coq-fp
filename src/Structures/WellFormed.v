Require Import FP.Data.Type.
Require Import FP.Structures.Multiplicative.

Import MultiplicativeNotation.

Class WellFormed T :=
  { wf : T -> Prop }.

Definition with_wf (T:Type) {WF:WellFormed T} : Prop := exists t:T, wf t.