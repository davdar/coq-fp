Require Import Data.BoolPre.
Require Import Data.Function.
Require Import Relations.RelDec.

Import FunctionNotation.

Class EqDec T := { eq_dec : T -> T -> bool }.

Section EqDec.
  Context {T} {E:EqDec T}.

  Global Instance Eq_RelDec : RelDec eq_dec eq.

  Definition neg_eq_dec := negb <..> eq_dec.

  Context {RDC:RelDecCorrect eq_dec eq}.

  Definition eq_dec_p : forall x y:T, {x=y}+{x<>y} := rel_dec_p.
  Definition neg_eq_dec_p : forall x y:T, {x<>y}+{x=y} := neg_rel_dec_p.
End EqDec.

Module EqDecNotation.
  Infix "'=!" := eq_dec (at level 35, no associativity).
  Infix "'/=!" := neg_eq_dec (at level 35, no associativity).

  Infix "'=?" := eq_dec_p (at level 35, no associativity).
  Infix "'/=?" := neg_eq_dec_p (at level 35, no associativity).
End EqDecNotation.

