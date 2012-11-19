Require Import Data.ListPre.

Require Import Structures.Eqv.

Import EqvNotation.

(* A category with an associative product *)
Class Semigroup g :=
  { gtimes : g -> g -> g }.

(* A semigroup with an identity *)
Class Monoid g :=
  { Monoid_Semigroup :> Semigroup g
  ; gunit : g
  }.

(* Also called a group *)
Class InverseMonoid g :=
  { InverseMonoid_Monoid :> Monoid g
  ; ginv : g -> g      (* derivable from gdiv *)
  ; gdiv : g -> g -> g (* derivable from ginv *)
  }.

(* An Abelian group is an invers monoid which is commutative *)
  

Module MonoidNotation.
  Infix "**" := gtimes (at level 45, right associativity).
End MonoidNotation.
Import MonoidNotation.

Class MonoidLaws g {E:Eqv g} {M:Monoid g} :=
{ monoid_identity : forall t, gunit ** t '~= t
; monoid_associativity : forall t1 t2 t3, (t1 ** t2) ** t3 '~= t1 ** (t2 ** t3)
}.

Section Monoid.
  Context {t} {M:Monoid t}.

  Definition gproductr := foldr gtimes gunit.
  Definition gproductl := foldl gtimes gunit.
End Monoid.
