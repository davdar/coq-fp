Require Import FP.CoreData.Bool.
Require Import FP.CoreData.Function.
Require Import FP.CoreClasses.Injection.
Require Import FP.CoreClasses.Eqv.
Require Import FP.CoreClasses.Setoid.
Require Import FP.CoreClasses.PartialOrd.
Require Import FP.CoreClasses.RelDec.
Require Import FP.CoreClasses.PreOrd.

Import BoolNotation.
Import FunctionNotation.
Import ProperNotation.

Class TotalOrd T `{! Lte T ,! Eqv T ,! ER_WF T } :=
  { TotalOrd_PartialOrd :> PartialOrd T
  ; TotalOrd_comparable : forall x y, ~(~lte x y /\ ~lte y x)
  }.

Class TotalOrdDec T := { tord_dec : T -> T -> comparison}.

Class TotalOrd_RDC T `{! Lte T ,! Eqv T ,! ER_WF T ,! TotalOrd T ,! TotalOrdDec T} :=
  { tord_rel_correct_eqv : forall {x:T} {y:T}, eqv x y -> tord_dec x y = Eq
  ; tord_rel_correct_lt : forall {x:T} {y:T}, lt x y -> tord_dec x y = Lt
  ; tord_rel_correct_gt : forall {x:T} {y:T}, lt y x -> tord_dec x y = Gt
  ; tord_dec_correct_eqv : forall {x:T} {y:T}, tord_dec x y = Eq -> eqv x y
  ; tord_dec_correct_lt : forall {x:T} {y:T}, tord_dec x y = Lt -> lt x y
  ; tord_dec_correct_gt : forall {x:T} {y:T}, tord_dec x y = Gt -> lt y x
  }.

Module TotalOrdNotation.
  Notation "x <=>! y"      := (tord_dec x y)
    (at level 35, no associativity).

  (*
  Notation "x <=>? y"      := (tord_dec_p x y)
    (at level 35, no associativity).
*)
End TotalOrdNotation.