Require Import FP.Data.Function.
Require Import FP.Structures.Eqv.
Require Import FP.Relations.Setoid.
Require Import FP.Relations.Function.

Import FunctionNotation.
Import ProperNotation.

Section Eqv.
  Context {A} {A_Eqv:Eqv A}.
  Context {B} {B_Eqv:Eqv B}.
  Global Instance function_Eqv : Eqv (A -> B) :=
    { eqv := (eqv ==> eqv) }.
End Eqv.