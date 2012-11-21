Require Import FP.Data.Identity.
Require Import FP.Data.Susp.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Monad.
Require Import FP.Data.FunctionPre.
Require Import FP.Data.Option.
Require Import FP.Data.Cont.
Require Import FP.Structures.MonadCont.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Functor.

Import MonadNotation.
Import FunctionNotation.
Import SuspNotation.
Import EqvNotation.

Class Foldable A T :=
  { cofold : forall {m} {M:Comonad m} {B}, (A -> m B -> B) -> m B -> T -> B }.

Section Foldable.
  Context {T A} {F:Foldable A T}.

  Definition fold {B} (f:A -> B -> B) (b:B) : T -> B :=
    cofold (fun (a:A) (bM:identity B) => f a $ run_identity bM) (Identity b).

  Definition mfold {m} {M:Monad m} {B}
      (f:A -> B -> m B) (b:B) : T -> m B :=
    fold (fun (a:A) (bM:m B) => b <- bM ;; f a b) (ret b).

  Definition revfold {B}
      (f:A -> B -> B) : B -> T -> B :=
    run_cont <..> 
      mfold begin fun (a:A) (b:B) =>
        callcc $ fun (k:B -> cont B B) =>
          b <- k b ;;
          ret $ f a b
      end.
  
  Definition lazyfold {B}
    (f:forall {C}, A -> (C -> B) -> C -> B) (b:B) : T -> B :=
    cofold (fun (a:A) (bM:susp B) => f a force bM) (delay | b).
End Foldable.

Section Fix.
  Context {T} {F:Foldable T T}.

  Definition fold_fix {A B}
      (ff:(T -> A -> option B) -> T -> A -> option B) (t:T) (a:A) : option B :=
    lazyfold (fun _ a k l => ff $ fun _ b => k l a b) (const2 None) t t a.

  Definition fold_mfix {m} {M:Monad m} {A B}
      (ff:(T -> A -> m (option B)) -> T -> A -> m (option B)) (t:T) (a:A)
      : m (option B) :=
    lazyfold (fun _ a k l => ff $ fun _ b => k l a b) (const2 $ ret None) t t a.
End Fix.

Class Buildable A T :=
  { build : (forall B, (A -> B -> B) -> B -> B) -> T }.

Section GeneralizedList.
  Definition map {T A U B} {TF:Foldable A T} {UB:Buildable B U}
      (f:A -> B) (t:T) : U :=
    build $ fun C (cons:B -> C -> C) (nil:C) =>
      fold (fun (a:A) (c:C) => cons (f a) c) nil t.

  Definition select {T A} {TF:Foldable A T} (p:A -> bool) : T -> option A :=
    lazyfold begin fun C (a:A) (k:C -> option A) (l:C) =>
      if p a then Some a else k l
    end None.

  Definition lookup {T A B} {E:EqvDec A} {TF:Foldable (A*B) T} (a:A)
      : T -> option B :=
    fmap snd <.> select (fun (p:A*B) => fst p '~=! a).
  
End GeneralizedList.

