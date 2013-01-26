Require Import FP.Data.Function.

Require Import FP.Relations.RelDec.
Require Import FP.Structures.Injection.
Require Import FP.Relations.Setoid.

Import FunctionNotation.

Class Eqv T := { eqv : T -> T -> Prop }.
Arguments eqv {T Eqv} _ _ : simpl never.

Section Eqv.
  Context {T} {T_Eqv:Eqv T}.

  Definition not_eqv : T -> T -> Prop := not '..' eqv.
End Eqv.

Class EqvWF T {T_Eqv:Eqv T} := { eqv_equivalence :> Equivalence eqv}.

Class EqvDec T := { eqv_dec : T -> T -> bool }.
Section EqvDec.
  Context {T} {T_EqvDec:EqvDec T}.

  Definition neg_eqv_dec : T -> T -> bool := negb '..' eqv_dec.

  Context {T_Eqv:Eqv T}.

  Context {eqv_RDC:RelDecCorrect T eqv eqv_dec}.

  Definition eqv_dec_p : forall x y:T, {eqv x y} + {~eqv x y} := rel_dec_p.
  Definition neg_eqv_dec_p : forall x y:T, {~eqv x y} + {eqv x y} := neg_rel_dec_p.
End EqvDec.
Arguments eqv_dec {T EqvDec} _ _ : simpl never.

Module EqvNotation.
  Infix "~=!" := eqv_dec (at level 35, no associativity).
  Infix "/~=!" := neg_eqv_dec (at level 35, no associativity).

  Infix "~=?" := eqv_dec_p (at level 35, no associativity).
  Infix "/~=?" := neg_eqv_dec_p (at level 35, no associativity).

  Infix "~=" := eqv (at level 70, no associativity).
  Infix "/~=" := not_eqv (at level 70, no associativity).
End EqvNotation.
Import EqvNotation.

