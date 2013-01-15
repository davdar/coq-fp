Require Import FP.Structures.Injection.
Require Import FP.Structures.Eqv.

Import EqvNotation.

Class Isomorphism A B {AE:Eqv A} {BE:Eqv B} :=
  { isomorphism_bijection :> Bijection A B
  ; isomorphism_eqv_from : forall {a:A}, a ~= from (to a)
  ; isomorphism_eqv_to : forall {b:B}, b ~= to (from b)
  }.