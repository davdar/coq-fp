Require Import Data.Function.
Require Import Structures.Buildable.
Require Import Structures.Eqv.
Require Import Structures.Functor.
Require Import Data.Option.
Require Import Structures.Foldable.
Require Import Structures.Monad.
Require Import Structures.Peano.
Require Import Data.State.

Import MonadNotation.
Import EqvNotation.
Import FunctionNotation.

Definition map {A B T U} {TF:FoldableR A T} {UB:BuildableR B U} (f:A -> B) (t:T) : U :=
  buildr $ fun cons nil =>
    foldr (fun a u => f a `cons` u) nil t.

Definition foreach {A B T U} {TF:FoldableR A T} {UB:BuildableR B U} : T -> (A -> B) -> U := flip map.

Definition select {A T} {F:FoldableR A T} (p:A -> bool) : T -> option A :=
  flip lazyfoldr None $ fun _ a k l => 
    if p a then
      Some a
    else
      k l.

Definition lookup {A B T} {E:EqvDec A} {F:FoldableR (A*B) T} (k:A) : T -> option B :=
  fmap snd <.> select (fun x => let '(k', v) := x in k' '~=! k).

Definition cat_options {A T U} {TF:FoldableR (option A) T} {TB:BuildableR A U} (t:T) : U :=
  buildr $ fun cons nil =>
    foldr (fun xM xs =>
             match xM with
             | None => xs
             | Some x => x `cons` xs
             end) nil t.

Definition numbered {A P T U} {PP:Peano P} {F:FoldableR A T} {B:BuildableR (P*A) U} (t:T) : U :=
  buildr $ fun cons nil =>
    eval_state pzero $
      mfoldr (fun (a:A) (u:U) =>
                i <- pinc ;;
                ret $ (i,a) `cons` u) nil t.

Definition concat {A T U V} {TF:FoldableR U T} {UF:FoldableR A U} {VF:FoldableR A V} {VB:BuildableR A V} (t:T) : V :=
  buildr $ fun cons nil =>
    foldr (fun u v => foldr cons v (foldr cons nil u)) nil t.