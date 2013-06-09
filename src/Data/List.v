Require Import FP.CoreData.
Require Import FP.Classes.

Import CoreDataNotation.
Import ClassesNotation.

Instance list_GUnit {A} : GUnit (list A) := { gunit := [] }.
Instance list_GTimes {A} : GTimes (list A) := { gtimes := app }.

Fixpoint list_cofold {X w} `{! Comonad w } {A} (f:X -> w A -> A) (aW:w A) (xs:list X) : A :=
  match xs with
  | [] => coret aW
  | x::xs =>
      let aW := codo aW => list_cofold f aW xs in
      f x aW
  end.
Instance list_Foldable {X} : Foldable X (list X) :=
  { cofold := @list_cofold X }.

Fixpoint list_coiter {X w} `{! Comonad w } {A} (f:w A -> X -> A) (aW:w A) (xs:list X) : A :=
  match xs with
  | [] => coret aW
  | x::xs =>
      let aW := codo aW => f aW x in
      list_coiter f aW xs
  end.
Instance list_Iterable {X} : Iterable X (list X) :=
  { coiter := @list_coiter X }.

Fixpoint list_mbuild {X m} `{! Monad m } (fld:forall {A}, (X -> A -> A) -> A -> m A) : m (list X) :=
  fld cons nil.
Instance list_Buildable {X} : Buildable X (list X) :=
  { mbuild := @list_mbuild X }.

Fixpoint list_sequence {u} `{! Applicative u } {A}
    (xs:list (u A)) : u (list A) :=
  match xs with
  | nil => fret nil
  | x::xs' => fret cons <@> x <@> list_sequence xs'
  end.
Instance list_Traversable : Traversable list :=
  { tsequence := @list_sequence }.