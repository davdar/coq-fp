Require Import FP.Classes.Monad.
Require Import FP.Classes.PFunctor.

Definition functor_t := Type -> Type.
Definition functor_morphism (t u:functor_t) := forall A, t A -> u A.
Module MorphismNotation.
  Infix "->>" := functor_morphism (at level 80, right associativity).
End MorphismNotation.
Import MorphismNotation.

Class Monad2 _M_ :=
  { m2ret : forall {m} `{! Monad m }, m ->> _M_ m
  ; m2extend : forall {m n} `{! Monad m ,! Monad n }, (m ->> _M_ n) -> _M_ m ->> _M_ n
  }.

Class PFunctor2 _T_ :=
  { pf2ret : forall {t} `{! PFunctor t }, t ->> _T_ t
  ; pf2map : forall {t u} `{! PFunctor t ,! PFunctor u }, (t ->> u) -> _T_ t ->> _T_ u
  }.
