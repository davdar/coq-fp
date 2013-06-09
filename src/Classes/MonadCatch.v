Require Import FP.CoreClasses.
Require Import FP.Classes.Monad.
Require Import FP.CoreData.

Import CoreClassesNotation.

Class MonadCatch E (m:Type->Type) :=
  { mthrow : forall {A}, E -> m A
  ; mcatch : forall {A}, m A -> (E -> m A) -> m A
  }.
Arguments mthrow {E m MonadCatch A} _ : simpl never.
Arguments mcatch {E m MonadCatch A} _ _ : simpl never.

Definition mtry {E m A} `{! MonadCatch E m } (aM1:m A) (aM2:m A) : m A :=
  mcatch aM1 (const aM2).
Arguments mtry {E m A _} aM1 aM2 : simpl never.

Module MonadCatchNotation.
  Infix "<|>" := mtry (at level 46, right associativity).
End MonadCatchNotation.
Import MonadCatchNotation.

Section MonadCatchWF.
  Context {E m} `{! Eqv E ,! PER_WF E ,! F_Eqv m ,! F_PER_WF m ,! Monad m ,! MonadCatch E m }.

  Class MonadCatchWF :=
    { MonadCatch_mcatch_mret :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (a:A) `{! Proper eqv a }
          (k:E -> m A) `{! Proper eqv k },
        mcatch (mret a) k ~= mret a
    ; MonadCatch_mcatch_mthrow :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (e:E) `{! Proper eqv e }
          (k:E -> m A) `{! Proper eqv k },
        mcatch (mthrow e) k ~= k e 
    ; MonadCatch_mbind_mthrow :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (e:E) `{! Proper eqv e }
          (k:A -> m B) `{! Proper eqv k },
        mbind (mthrow e) k ~= mthrow e
    ; mthrow_Proper :>
        forall {A} `{! Eqv A ,! PER_WF A },
        Proper eqv (mthrow (m:=m) (A:=A))
    ; mcatch_Proper :>
        forall {A} `{! Eqv A ,! PER_WF A },
        Proper eqv (mcatch (m:=m) (A:=A)) 
    }.

  Context `{! MonadCatchWF }.

  Definition MonadCatch_mtry_mret :
    forall
      {A} `{! Eqv A ,! PER_WF A }
      (a:A) `{! Proper eqv a }
      (aM: m A) `{! Proper eqv aM },
    mret a <|> aM ~= mret a. 
  Proof.
    intros ; unfold mtry ; apply MonadCatch_mcatch_mret ; logical_eqv.
  Qed.

  Definition MonadCatch_mtry_mthrow :
    forall
      {A} `{! Eqv A ,! PER_WF A }
      (e:E) `{! Proper eqv e }
      (aM:m A) `{! Proper eqv aM },
    mthrow e <|> aM ~= aM.
  Proof.
    intros ; unfold mtry ; apply MonadCatch_mcatch_mthrow ; logical_eqv.
  Qed.

  Global Instance mtry_Proper :
    forall {A} `{! Eqv A ,! PER_WF A },
    Proper eqv (mtry (m:=m) (A:=A)).
  Proof.
    intros ; unfold mtry ; logical_eqv.
  Qed.

End MonadCatchWF.
Arguments MonadCatchWF E m {_ _ _ _}.
