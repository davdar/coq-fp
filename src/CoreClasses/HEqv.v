Require Import FP.CoreClasses.Eqv.
Require Import FP.CoreClasses.Bijection.

Class HEqv T U := { heqv : T -> U -> Prop }.

(* does this need to be a class?  is HEqv even usefull?? what are the laws? *)
Instance : forall (T U:Type) `{! Eqv T ,! Eqv U ,! Bijection T U }, HEqv T U :=
  { heqv x y := eqv x (bij_from y) }.
