Require Import FP.Structures.Applicative.
Require Import FP.Data.Function.
Require Import FP.Structures.Functor.
Require Import FP.Structures.FunctorP.

Import FunctionNotation.
Import FunctorNotation.

Class Traversable t :=
  { tsequence : forall {u} {uA:Applicative u} {A}, t (u A) -> u (t A) }.

Definition tmap {t u} {tT:Traversable t} {tF:Functor t} {uA:Applicative u} {A B}
  (f:A -> u B) : t A -> u (t B) := tsequence '.' fmap f.

Definition tsequence2 {t u v}
    {tF:Functor t} {tT:Traversable t} {uT:Traversable u} {vA:Applicative v} {A}
    : t (u (v A)) -> v (t (u A)) :=
  tsequence '.' fmap tsequence.

Definition tforeach {t u} {T:Traversable t} {F:Functor t} {uA:Applicative u} {A B} :
    t A -> (A -> u B) -> u (t B) := flip tmap.

Class TraversableP P t :=
  { tsequence_p : forall {u} {uA:Applicative u} {A} {p:P A}, t (u A) -> u (t A) }.


Definition tmap_p {t tP u} {tT:TraversableP tP t} {tF:FunctorP tP t} {uA:Applicative u} {A B} {tp:tP B} {tup:tP (u B)}
  (f:A -> u B) : t A -> u (t B) :=
    fun x =>
      let y : t (u B) := fmap_p (p:=tup) f x in
      tsequence_p (p:=tp) y.
