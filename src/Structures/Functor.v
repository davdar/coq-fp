Require Import FP.Data.Function.

Import FunctionNotation.

Class Functor t := { fmap : forall {A B}, (A -> B) -> t A -> t B}.

Section Functor.
  Context {t u} {tF:Functor t} {uF:Functor u}.

  Definition fmap2 {A} {B} : (A -> B) -> u (t A) -> u (t B) := fmap '.' fmap.

  Context {v} {vF:Functor v}.

  Definition fmap3 {A} {B} : (A -> B) -> v (u (t A)) -> v (u (t B)) := fmap '.' fmap2.
End Functor.

Module FunctorNotation.
  Infix "<$>" := fmap (at level 46, left associativity).
  Infix "<$$>" := fmap2 (at level 46, left associativity).
  Infix "<$$$>" := fmap3 (at level 46, left associativity).
End FunctorNotation.

