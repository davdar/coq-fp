Require Import FP.Structures.Monoid.

Class GTimesLaws T {T_GTimes : GTimes T} :=
  { gtimes_associativity : Associative gtimes }.

Class GUnitLaws T {T_GTimes : GTimes T} {T_GUnit : GUnit T} :=
  { gunit_left_identity : forall (t:T), gunit ** t ~= t
  ; gunit_right_identity : forall (t:T), t ** gunit ~= t
  }.

Class GDivLaws T {T_GTimes : GTimes T} {T_GDiv : GDiv T} :=
  { gdiv_equation :
      forall (t1:T) (t2:T) (t3:T),
        t1 ** t2 ~= t3 <-> t1 ~= t3 // t2
  }.

Class GInvLaws T {T_GTimes : GTimes T} {T_GUnit : GUnit T} {T_GInv : GInv T} :=
  { ginv_identity : ginv gunit ~= gunit
  ; ginv_div : forall (t1:T) (t2:T), t1 ** ginv t2 ~= t1 // t2
  }.

Class MonoidLaws g {E:Eqv g} {M:Monoid g} :=
{ monoid_identity : forall t, gunit ** t '~= t
; monoid_associativity : forall t1 t2 t3, (t1 ** t2) ** t3 '~= t1 ** (t2 ** t3)
}.
