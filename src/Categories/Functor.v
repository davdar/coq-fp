Require Import FP.CoreData.
Require Import FP.CoreClasses.

Import FunctionNotation.
Import ProperNotation.
Import EqvNotation.

Class FMap (t:Type->Type) : Type :=
  { fmap : forall {A B}, (A -> B) -> t A -> t B }.
Arguments fmap {t FMap A B} _ _ : simpl never.

Section FMap.
  Context {t u} `{! FMap t ,! FMap u}.

  Definition fmap2 {A} {B} : (A -> B) -> u (t A) -> u (t B) := fmap '.' fmap.

  Context {v} `{! FMap v }.

  Definition fmap3 {A} {B} : (A -> B) -> v (u (t A)) -> v (u (t B)) := fmap '.' fmap2.
End FMap.

Module FunctorNotation.
  Infix "<$>" := fmap (at level 46, left associativity).
  Infix "<$$>" := fmap2 (at level 46, left associativity).
  Infix "<$$$>" := fmap3 (at level 46, left associativity).
End FunctorNotation.

Section FunctorWF.
  Context {t} `{! FMap t ,! F_Eqv t ,! F_PER_WF t }.
  
  Class FunctorWF :=
    { fmap_id :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (f:A -> A) `{! Proper eqv f }
          (aT:t A) `{! Proper eqv aT },
        fmap id aT ~= aT
    ; fmap_compose :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          {C} `{! Eqv C ,! PER_WF C }
          (f:A -> B) `{! Proper eqv f }
          (g:B -> C) `{! Proper eqv g }
          (aT:t A) `{! Proper eqv aT },
        fmap (g '.' f) aT ~= (fmap g '.' fmap f) aT
    ; fmap_respect :>
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B },
        Proper eqv (fmap (A:=A) (B:=B))
    }.
End FunctorWF.
Arguments FunctorWF t {_ _}.