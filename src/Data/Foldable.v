Require Import FP.Classes.
Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Data.Identity.
Require Import FP.Data.Cont.
Require Import FP.Data.Susp.
Require Import FP.Data.Option.
Require Import FP.Data.Peano.
Require Import FP.Data.N.
Require Import FP.Data.State.

Import CoreDataNotation.
Import CoreClassesNotation.
Import ClassesNotation.
Import SuspNotation.

Section Foldable.
  Context {X T} `{! Foldable X T }.

  Definition fold {A} (f:X -> A -> A) (a:A) : T -> A :=
    cofold (fun (x:X) (aM:identity A) => f x $ run_identity aM) (Identity a).
  Definition mfold {m A} `{! Monad m } (f:X -> A -> m A) (a:A) : T -> m A :=
    fold (fun (x:X) (aM:m A) => a <- aM ;; f x a) (mret a).
  Definition revfold {A} (f:X -> A -> A) : A -> T -> A :=
    run_cont '.:' 
      mfold begin fun (x:X) (a:A) =>
        callcc $ fun (k:A -> cont A A) =>
          a <- k a ;;
          mret $ f x a
      end.
  Definition lazyfold {A} (f:forall {C}, X -> (C -> A) -> C -> A) (a:A) : T -> A :=
    cofold (fun (x:X) (aW:susp A) => f x force aW) (delay | a).
End Foldable.

Section Fix.
  Context {T} {F:Foldable T T}.

  Definition fold_fix {A B}
      (ff:(T -> A -> option B) -> T -> A -> option B) (t:T) (a:A) : option B :=
    lazyfold begin fun (C:Type) (t:T) (k:C->T->A->option B) (l:C) =>
      ff $ fun _ (a:A) => k l t a
    end (const2 None) t t a.

  Definition fold_mfix {m A B} `{! Monad m }
      (ff:(T -> A -> m (option B)) -> T -> A -> m (option B)) (t:T) (a:A) : m (option B) :=
    lazyfold begin fun (C:Type) (t:T) (k:C->T->A->m (option B)) (l:C) =>
      ff $ fun _ (a:A) => k l t a
    end (const2 $ mret None) t t a.
End Fix.

Section Iterable.
  Context {X T} `{! Iterable X T }.

  Definition iter {A} (f:A -> X -> A) (a:A) : T -> A :=
    coiter (fun (aM:identity A) (x:X) => f (run_identity aM) x) (Identity a).
  Definition miter {m A} `{! Monad m } (f:A -> X -> m A) (a:A) : T -> m A :=
    iter (fun (aM:m A) (x:X) => a <- aM ;; f a x) (mret a).
  Definition reviter {A} (f:A -> X -> A) : A -> T -> A :=
    run_cont '.:'
      miter begin fun (a:A) (x:X) =>
        callcc $ fun (k:A -> cont A A) =>
          a <- k a ;;
          mret $ f a x
      end.
  Definition lazyiter {A} (f:forall {C}, (C -> A) -> X -> C -> A) (a:A) : T -> A :=
    coiter (fun (aW:susp A) (x:X) => f force x aW) (delay | a).
End Iterable.

Section Buildable.
  Context {X T} `{! Buildable X T }.

  Definition build (f:forall A, (X -> A -> A) -> A -> A) : T :=
    run_identity $ mbuild $
      fun A (f':X -> A -> A) (a:A) =>
        mret $ f A begin fun (x:X) (a:A) =>
          f' x a
        end a.
End Buildable.

Section GeneralizedList.
  Definition map {T A U B} `{! Foldable A T ,! Buildable B U }
      (f:A -> B) (t:T) : U :=
    build $ fun C (cons:B -> C -> C) (nil:C) =>
      fold (fun (a:A) (c:C) => cons (f a) c) nil t.

  Definition foreach {T A U B} `{! Foldable A T ,! Buildable B U }
      : T -> (A -> B) -> U := flip map.

  Definition filter {T A U} `{! Foldable A T ,! Buildable A U }
      (f:A -> bool) (t:T) : U :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      fold (fun (a:A) (c:C) => if f a then cons a c else c) nil t.

  Definition select {T A} `{! Foldable A T } (p:A -> bool) : T -> option A :=
    lazyfold begin fun C (a:A) (k:C -> option A) (l:C) =>
      if p a then Some a else k l
    end None.

  Definition lookup {T A B} `{! EqvDec A ,! Foldable (A*B) T } (a:A)
      : T -> option B :=
    mbind_fmap snd '.' select (fun (p:A*B) => fst p ~=! a).
  
  Definition cat_options {T A U} `{! Foldable (option A) T ,! Buildable A U }
      (t:T) : U :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      fold (fun (aM:option A) (c:C) => option_elim aM id cons c) nil t.

  Definition numbered {T A U} `{! Foldable A T ,! Buildable (N*A) U }
      (t:T) : U :=
    eval_state 0 $ mbuild $ fun C (cons:N*A -> C -> C) (nil:C) =>
      mfold begin fun (a:A) (c:C) =>
        n <- pinc ;;
        mret $ cons (n,a) c
      end nil t.

  Definition intersperse {T A U} `{! Foldable A T ,! Buildable A U }
      (i:A) (t:T) : U :=
    eval_state false $ mbuild $ fun C (cons:A -> C -> C) (nil:C) =>
      mfold begin fun (a:A) (c:C) =>
        b <- mget ;;
        mput true ;;
        mret $ if b:bool then
          cons a (cons i c)
        else
          cons a c 
      end nil t.

  Definition replicate {T A} `{! Buildable A T } (n:N) (a:A) : T :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      loopr (cons a) nil n.

  Definition length {T A P} `{! Foldable A T ,! Peano P } (t:T) : P :=
    exec_state pzero $
      mfold begin fun (_:A) (_:unit) =>
        pinc ;; mret tt
      end tt t.
End GeneralizedList.