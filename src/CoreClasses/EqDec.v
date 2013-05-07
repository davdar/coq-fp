Require Import FP.CoreData.Bool.
Require Import FP.CoreData.Function.
Require Import FP.CoreClasses.RelDec.

Import FunctionNotation.

Class EqDec T := { eq_dec : T -> T -> bool }.
Class Eq_RDC T `{! EqDec T } := { eq_rdc :> RelDecCorrect T eq eq_dec }.

Section EqDec.
  Context {T} `{! EqDec T }.

  Definition neg_eq_dec := negb '.:' eq_dec.

  Context `{! Eq_RDC T }.

  Definition eq_dec_p : forall x y:T, {x=y}+{x<>y} := rel_dec_p.
  Definition neg_eq_dec_p : forall x y:T, {x<>y}+{x=y} := neg_rel_dec_p.
End EqDec.

Module EqDecNotation.
  Infix "=!" := eq_dec (at level 35, no associativity).
  Infix "/=!" := neg_eq_dec (at level 35, no associativity).

  Infix "=?" := eq_dec_p (at level 35, no associativity).
  Infix "/=?" := neg_eq_dec_p (at level 35, no associativity).
End EqDecNotation.