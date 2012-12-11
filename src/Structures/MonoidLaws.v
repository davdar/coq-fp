Require Import FP.Data.Function.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Eqv.

Import EqvNotation.
Import FunctionNotation.
Import MonoidNotation.

Class GTimesLaws T {T_GTimes : GTimes T} {T_Eqv : Eqv T} :=
  { gtimes_associativity :
      forall t1 t2 t3, t1 ** (t2 ** t3) ~= (t1 ** t2) ** t3
  }.

Class GUnitLaws T {T_GTimes : GTimes T} {T_GUnit : GUnit T} {T_Eqv : Eqv T} :=
  { gunit_left_identity : forall t, gunit ** t ~= t
  ; gunit_right_identity : forall t, t ** gunit ~= t
  }.

Class GDivLaws T {T_GTimes : GTimes T} {T_GDiv : GDiv T} {T_Eqv : Eqv T} :=
  { gdiv_equation : forall (t1:T) (t2:T) (t3:T), t1 ** t2 ~= t3 <-> t1 ~= t3 // t2 }.

Class GInvLaws T {T_GTimes : GTimes T} {T_GUnit : GUnit T} {T_GInv : GInv T}
    {T_GDiv : GDiv T} {T_Eqv : Eqv T }:=
  { ginv_identity : ginv gunit ~= gunit
  ; ginv_div : forall (t1:T) (t2:T), t1 ** ginv t2 ~= t1 // t2
  }.

Class MonoidLaws T {E:Eqv T} {M:Monoid T} :=
  { monoid_laws_GTimesLaws :> GTimesLaws T
  ; monoid_laws_GUnitLaws :> GUnitLaws T
  }.
