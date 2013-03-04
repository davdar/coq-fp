Require Import FP.Data.Function.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.FunctorP.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Applicative.

Import FunctionNotation.
Import FunctorNotation.

Class Traversable t :=
  { tsequence : forall {u} {uA:Applicative u} {A}, t (u A) -> u (t A) }.

Definition tmap {t u} {tT:Traversable t} {tF:FMap t} {uA:Applicative u} {A B}
  (f:A -> u B) : t A -> u (t B) := tsequence '.' fmap f.

Definition tsequence2 {t u v}
    {tF:FMap t} {tT:Traversable t} {uT:Traversable u} {vA:Applicative v} {A}
    : t (u (v A)) -> v (t (u A)) :=
  tsequence '.' fmap tsequence.

Definition tforeach {t u} {T:Traversable t} {F:FMap t} {uA:Applicative u} {A B} :
    t A -> (A -> u B) -> u (t B) := flip tmap.

Class TraversableP P t :=
  { tsequence_p : forall {u} {uA:Applicative u} {A} {p:Proxy2 P A}, t (u A) -> u (t A) }.


Definition tmap_p {t tP u} {tT:TraversableP tP t} {tF:FMapP tP t} {uA:Applicative u} {A B} {tp:Proxy2 tP B} {tup:Proxy2 tP (u B)}
  (f:A -> u B) : t A -> u (t B) :=
    fun x =>
      let y : t (u B) := fmap_p f x in
      tsequence_p y.
