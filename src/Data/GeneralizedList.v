Require Import FP.Data.Function.
Require Import FP.Data.N.
Require Import FP.Data.NStructures.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.Peano.
Require Import FP.Data.State.
Require Import FP.Data.Option.

Import FunctionNotation.
Import EqvNotation.
Import MonadNotation.
Import NNotation.

Section GeneralizedList.
  Definition map {T A U B} {TF:Foldable A T} {UB:Buildable B U}
      (f:A -> B) (t:T) : U :=
    build $ fun C (cons:B -> C -> C) (nil:C) =>
      fold (fun (a:A) (c:C) => cons (f a) c) nil t.

  Definition foreach {T A U B} {TF:Foldable A T} {UB:Buildable B U}
      : T -> (A -> B) -> U := flip map.

  Definition filter {T A U} {TF:Foldable A T} {UB:Buildable A U}
      (f:A -> bool) (t:T) : U :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      fold (fun (a:A) (c:C) => if f a then cons a c else c) nil t.

  Definition select {T A} {TF:Foldable A T} (p:A -> bool) : T -> option A :=
    lazyfold begin fun C (a:A) (k:C -> option A) (l:C) =>
      if p a then Some a else k l
    end None.

  Definition lookup {T A B} {E:EqvDec A} {TF:Foldable (A*B) T} (a:A)
      : T -> option B :=
    bind_fmap snd '.' select (fun (p:A*B) => fst p ~=! a).
  
  Definition cat_options {T A U} {TF:Foldable (option A) T} {UB:Buildable A U}
      (t:T) : U :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      fold (fun (aM:option A) (c:C) => fold cons c aM) nil t.

  Definition numbered {T A U} {TF:Foldable A T} {UB:Buildable (N*A) U}
      (t:T) : U :=
    eval_state 0 $ mbuild $ fun C (cons:N*A -> C -> C) (nil:C) =>
      mfold begin fun (a:A) (c:C) =>
        n <- get ;;
        modify psucc ;;
        ret $ cons (n,a) c
      end nil t.

  Definition intersperse {T A U} {TF:Foldable A T} {UB:Buildable A U}
      (i:A) (t:T) : U :=
    eval_state false $ mbuild $ fun C (cons:A -> C -> C) (nil:C) =>
      mfold begin fun (a:A) (c:C) =>
        b <- get ;;
        put true ;;
        ret $ if b:bool then
          cons a (cons i c)
        else
          cons a c 
      end nil t.

  Definition replicate {T A} {TB:Buildable A T} (n:N) (a:A) : T :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      loopr (cons a) nil n.

  Definition length {T A} {TF:Foldable A T} {P} {Peano:Peano P} (t:T) : P :=
    exec_state pzero $
      mfold begin fun (_:A) (_:unit) =>
        pinc ;; ret tt
      end tt t.
End GeneralizedList.
