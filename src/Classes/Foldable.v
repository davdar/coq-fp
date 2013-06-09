Require Import FP.Classes.Comonad.
Require Import FP.Classes.Monad.
Require Import FP.CoreData.

Import CoreDataNotation.

Class Foldable X T :=
  { cofold : forall {w} `{! Comonad w } {A}, (X -> w A -> A) -> w A -> T -> A }.
Class Iterable X T :=
  { coiter : forall {w} `{! Comonad w } {A}, (w A -> X -> A) -> w A -> T -> A }.
Class Buildable X T :=
  { mbuild : forall {m} `{! Monad m }, (forall A, (X -> A -> A) -> A -> m A) -> m T }.