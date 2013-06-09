Require Import FP.CoreClasses.
Require Import FP.Classes.Monad.

Import CoreClassesNotation.
Import MonadNotation.

Class MonadPlus (m:Type->Type) :=
  { mzero : forall {A}, m A
  ; mplus : forall {A}, m A -> m A -> m A
  }.
Arguments mzero {m MonadPlus A} : simpl never.
Arguments mplus {m MonadPlus A} _ _ : simpl never.

Module MonadPlusNotation.
  Infix "<+>" := mplus (at level 46, right associativity).
End MonadPlusNotation.
Import MonadPlusNotation.

Section MonadPlusWF.
  Context {m} `{! F_Eqv m ,! F_PER_WF m ,! Monad m ,! MonadPlus m }.

  Class MonadPlusWF :=
    { MonadPlus_left_zero :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (aM:m A) `{! Proper eqv aM },
         mplus mzero aM ~= aM
    ; MonadPlus_right_zero :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (aM:m A) `{! Proper eqv aM },
        mplus aM mzero ~= aM
    ; MonadPlus_distribute :
        forall 
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (aM1:m A) `{! Proper eqv aM1 }
          (aM2:m A) `{! Proper eqv aM2 }
          (k:A -> m B) `{! Proper eqv k },
        (aM1 <+> aM2) >>= k ~= (aM1 >>= k) <+> (aM2 >>= k)
    }.
End MonadPlusWF.