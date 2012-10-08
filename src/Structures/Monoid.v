Require Import Data.List.
Require Import Structures.Eqv.
Require Import Structures.Pointed.

Import EqvNotation.

Class Monoid T :=
{ monoid_Pointed :> Pointed T
; monoid_times : T -> T -> T
}.

Module MonoidNotation.
  Infix "**" := monoid_times (at level 45, right associativity).
End MonoidNotation.
Import MonoidNotation.

Class MonoidLaws T {E:Eqv T} {M:Monoid T} :=
{ monoid_identity : forall t, top ** t ~= t
; monoid_associativity : forall t1 t2 t3, (t1 ** t2) ** t3 ~= t1 ** (t2 ** t3)
}.

Section Monoid.
  Context {T} {M:Monoid T}.

  Definition monoid_product := foldr monoid_times top.
End Monoid.