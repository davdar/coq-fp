Require Import FP.Data.Bool.
Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.EqvRel.
Require Import FP.Relations.Setoid.

Import FunctionNotation.
Import ProperNotation.

Class EqDec T := { eq_dec : T -> T -> bool }.

Section EqDec.
  Context {T} {E:EqDec T}.

  Definition neg_eq_dec := negb '..' eq_dec.

  Context {RDC:RelDecCorrect T eq eq_dec}.

  Definition eq_dec_p : forall x y:T, {x=y}+{x<>y} := rel_dec_p.
  Definition neg_eq_dec_p : forall x y:T, {x<>y}+{x=y} := neg_rel_dec_p.
End EqDec.

Module EqDecNotation.
  Infix "=!" := eq_dec (at level 35, no associativity).
  Infix "/=!" := neg_eq_dec (at level 35, no associativity).

  Infix "=?" := eq_dec_p (at level 35, no associativity).
  Infix "/=?" := neg_eq_dec_p (at level 35, no associativity).
End EqDecNotation.