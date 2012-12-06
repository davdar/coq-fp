Require Import FP.Data.Function.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Injection.

Import EqvNotation.
Import FunctionNotation.

Class Monad m :=
  { ret : forall {A}, A -> m A
  ; bind : forall {A B}, m A -> (A -> m B) -> m B
  }.
Local Infix ">>=" := bind (at level 50, left associativity).

Section Monad.
  Context {m} {M:Monad m}.

  Definition revbind {A B} : (A -> m B) -> m A ->  m B := flip bind.
  Definition kleisli_compose {A B C} (g:B -> m C) (f:A -> m B) (a:A) : m C :=
    f a >>= g.
  Definition kleisli_revcompose {A B C} : (A -> m B) -> (B -> m C) -> A -> m C :=
    flip kleisli_compose.

  Definition join {A} : m (m A) -> m A := revbind id.
  Definition mmap {A B} : (A -> B) -> m A -> m B :=
    revbind '.' compose ret.
  Definition mapply {A B} (fM:m (A -> B)) (aM:m A) : m B :=
    fM >>= flip mmap aM.

  Global Instance Monad_Applicative : Applicative m :=
    { fret := @ret _ _
    ; fapply := @mapply
    }.

  Section iso_Monad.
    Variable n:Type -> Type.
    Context {N:Monad n}.
    Context {m_n_FBij:FunctorBijection m n}.

    Definition iso_ret {A} : A -> m A := ffrom '.' ret.
    Definition iso_bind {A B} (aM:m A) (f:A -> m B) : m B := ffrom $ bind (fto aM) (fto '.' f).

    Definition iso_Monad : Monad m :=
      {| ret := @iso_ret
       ; bind := @iso_bind
      |}.
    End iso_Monad.
End Monad.

Module MonadNotation.
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity).

  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).

  Infix ">>=" := bind (at level 50, left associativity).
  Infix "=<<" := revbind (at level 51, right associativity).
  Infix "<=<" := kleisli_compose (at level 53, right associativity).
  Infix ">=>" := kleisli_revcompose (at level 53, right associativity).
End MonadNotation.
Import MonadNotation.

Class MonadLaws m {E:forall A {AE:Eqv A}, Eqv (m A)} {M:Monad m} :=
  { monad_bind_of_ret
      : forall {A B} {AE:Eqv A} {BE:Eqv B} {x:A} {f:A -> m B},
          ret x >>= f ~= f x
  ; monad_ret_of_bind
      : forall {A} {AE:Eqv A} {c:m A},
          c >>= ret ~= c
  ; monad_associativity
      : forall {A B c} {AE:Eqv A} {BE:Eqv B} {CE:Eqv c}
               {aM:m A} {f:A -> m B} {g:B -> m c},
          aM >>= f >>= g ~= aM >>= fun x => f x >>= g
  }.
