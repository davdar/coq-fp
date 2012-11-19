Require Export Data.FunctionPre.

Require Import Structures.Functor.
Require Import Structures.Monad.

Definition fun_ret {T A} : A -> T -> A := const.
Definition fun_bind {T A B} (aM:T -> A) (f:A -> T -> B) (t:T) : B :=
  let a := aM t in
  f a t.
Definition Fun_Monad {T} : Monad (Fun T) :=
  {| ret _A := fun_ret
   ; bind _A _B := fun_bind (T:=T)
  |}.

