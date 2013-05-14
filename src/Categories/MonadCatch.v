Require Import FP.CoreClasses.
Require Import FP.Categories.Monad.
Require Import FP.CoreData.

Import CoreClassesNotation.

Class MCatch E (m:Type->Type) :=
  { mthrow : forall {A}, E -> m A
  ; mcatch : forall {A}, m A -> (E -> m A) -> m A
  }.
Arguments mthrow {E m MCatch A} _ : simpl never.
Arguments mcatch {E m MCatch A} _ _ : simpl never.

Definition mtry {E m A} `{! MCatch E m } (aM1:m A) (aM2:m A) : m A :=
  mcatch aM1 (const aM2).

Module MonadCatchNotation.
  Infix "<|>" := mtry (at level 46, right associativity).
End MonadCatchNotation.

Section MonadCatchWF.
  Context {E m} `{! Eqv E ,! PER_WF E ,! F_Eqv m ,! F_PER_WF m ,! MBind m ,! MCatch E m }.

  Class MonadCatchWF :=
    { mcatch_throw_zero :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (e:E) `{! Proper eqv e }
          (k:E -> m A) `{! Proper eqv k },
        mcatch (mthrow e) k ~= k e 
    ; mcatch_bind_zero :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (e:E) `{! Proper eqv e }
          (k:A -> m B) `{! Proper eqv k },
        bind (mthrow e) k ~= mthrow e
    ; mthrow_Proper :>
        forall
          {A} `{! Eqv A ,! PER_WF A },
        Proper eqv (mthrow (m:=m) (A:=A))
    ; mcatch_Proper :>
        forall
          {A} `{! Eqv A ,! PER_WF A },
        Proper eqv (mcatch (m:=m) (A:=A)) 
    }.
End MonadCatchWF.
Arguments MonadCatchWF E m {_ _ _ _}.