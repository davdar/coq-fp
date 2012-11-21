Require Import FP.Structures.Comonad.
Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Structures.Monad.
Require Import FP.Data.Cont.
Require Import FP.Structures.MonadCont.
Require Import FP.Data.Susp.
Require Import FP.Structures.Monoid.

Import FunctionNotation.
Import MonadNotation.
Import SuspNotation.

Class Iterable A T :=
  { coiter : forall {m} {M:Comonad m} {B}, (m B -> A -> B) -> m B -> T -> B }.

Section Iterable.
  Context {T A} {F:Iterable A T}.

  Definition iter {B} (f:B -> A -> B) (b:B) : T -> B := 
    coiter (fun (bM:identity B) (a:A) => f (run_identity bM) a) (Identity b).

  Definition miter {m} {M:Monad m} {B} (f:B -> A -> m B) (b:B) : T -> m B :=
    iter (fun (bM:m B) (a:A) => b <- bM ;; f b a) (ret b).

  Definition reviter {B} (f:B -> A -> B) : B -> T -> B :=
    run_cont <..> 
      miter begin fun (b:B) (a:A) =>
        callcc $ fun (k:B -> cont B B) =>
          b <- k b ;;
          ret $ f b a
      end.

  Definition lazyiter {B}
      (f:forall {C}, (C -> B) -> C -> A -> B) (b:B) : T -> B :=
    coiter (fun (bM:susp B) (a:A) => f force bM a) (delay | b).
End Iterable.

Class TreeIterable A T :=
  { co_treeiter : forall {m} {M:Comonad m} {B} {BM:Monoid B},
                    (m B -> A -> B) -> m B -> T -> B
  }.

Section TreeIterable.
  Context {A T} {I:TreeIterable A T}.

  Definition treeiter {B} {BM:Monoid B} (f:B -> A -> B) (b:B) : T -> B :=
    co_treeiter (fun (bM:identity B) (a:A) => f (un_identity bM) a) (Identity b).
End TreeIterable.