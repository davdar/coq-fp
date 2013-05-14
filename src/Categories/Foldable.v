Require Import FP.Categories.Comonad.
Require Import FP.Categories.Copointed.
Require Import FP.Categories.Monad.
Require Import FP.Categories.Pointed.
Require Import FP.CoreData.

Import CoreDataNotation.

Class Foldable X T :=
  { cofold : forall {w} `{! Counit w ,! Cobind w } {A}, (X -> w A -> A) -> w A -> T -> A }.
Class Iterable X T :=
  { coiter : forall {w} `{! Counit w ,! Cobind w } {A}, (w A -> X -> A) -> w A -> T -> A }.
Class Buildable X T :=
  { mbuild : forall {m} `{! FUnit m ,! MBind m }, (forall A, (X -> A -> A) -> A -> m A) -> m T }.