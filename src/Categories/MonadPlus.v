Require Import FP.CoreClasses.
Require Import FP.Categories.Monad.

Import CoreClassesNotation.
Import MonadNotation.

Class MPlus (m:Type->Type) :=
  { mzero : forall {A}, m A
  ; mplus : forall {A}, m A -> m A -> m A
  }.

Module MonadPlusNotation.
  Infix "<+>" := mplus (at level 46, right associativity).
End MonadPlusNotation.
Import MonadPlusNotation.

Section MonadPlusWF.
  Context {m} `{! F_Eqv m ,! F_PER_WF m ,! MBind m ,! MPlus m }.

  Class MonadPlusWF :=
    { mplus_left_zero :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (aM:m A) `{! Proper eqv aM },
         mplus mzero aM ~= aM
    ; mplus_right_zero :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (aM:m A) `{! Proper eqv aM },
        mplus aM mzero ~= aM
    ; mplus_distribute :
        forall 
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (aM1:m A) `{! Proper eqv aM1 }
          (aM2:m A) `{! Proper eqv aM2 }
          (k:A -> m B) `{! Proper eqv k },
        (aM1 <+> aM2) >>= k ~= (aM1 >>= k) <+> (aM2 >>= k)
    }.
End MonadPlusWF.