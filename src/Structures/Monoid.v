Require Import Eqv.
Import EqvNotation.
Require Import Pointed.

Class Monoid T :=
{ monoid_Pointed :> Pointed T
; monoid_product : T -> T -> T
}.

Module MonoidNotation.
  Infix "**" := monoid_product (at level 45, right associativity).
End MonoidNotation.
Import MonoidNotation.

Class MonoidLaws T {E:Eqv T} {M:Monoid T} :=
{ monoid_identity : forall t, top ** t ~= t
; monoid_associativity : forall t1 t2 t3, (t1 ** t2) ** t3 ~= t1 ** (t2 ** t3)
}.