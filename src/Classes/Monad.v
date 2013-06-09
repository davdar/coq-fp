Require Import FP.CoreClasses.
Require Import FP.CoreData.

Import ProperNotation.
Import FunctionNotation.
Import EqvNotation.

Class Monad (m:Type->Type) :=
  { mret : forall {A}, A -> m A
  ; mbind : forall {A B}, m A -> (A -> m B) -> m B
  }.
Arguments mret {m Monad A} _ : simpl never.
Arguments mbind {m Monad A B} _ _ : simpl never.

Section Monad.
  Context {m} `{! Monad m }.

  Definition mextend {A B} : (A -> m B) -> (m A -> m B) := flip mbind.
  Definition mseq {A B} (aM:m A) (bM:m B) : m B := mbind aM (const bM).

  Definition mbind_mpipe {A B C} (f:A -> m B) (g:B -> m C) (a:A) : m C :=
    mbind (f a) g.
  Definition mbind_mjoin {A} (aMM:m (m A)) : m A :=
    mbind aMM id.
  Definition mbind_fmap {A B} (f:A -> B) (aM:m A) : m B :=
    mbind aM (mret '.' f).
  Definition mbind_fapply {A B} (fM:m (A -> B)) (aM:m A) : m B :=
    mbind fM (fun f => mbind aM (fun a => mret (f a))).
  Definition mbind_ftimes {A B} (aM:m A) (bM:m B) : m (A*B) :=
    mbind aM (fun a => mbind bM (fun b => mret (a,b))).
End Monad.
Arguments mextend {m _ A B} _ _ /.
Arguments mbind_mpipe {m _ A B C} f g a /.
Arguments mbind_mjoin {m _ A} aMM /.
Arguments mbind_fmap {m _ A B} f aM /.
Arguments mbind_fapply {m _ A B} fM aM /.
Arguments mbind_ftimes {m _ A B} aM bM /.

Module MonadNotation.
  Notation "x <- c1 ;; c2" := (mbind c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity).

  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).

  Infix ">>=" := mbind (at level 50, left associativity).
  Infix "=<<" := mextend (at level 51, right associativity).
  Infix ">>" := mseq (at level 50, left associativity).
End MonadNotation.
Import MonadNotation.

Section MonadWF.
  Context {m:Type->Type}.
  Context `{! Monad m ,! F_Eqv m ,! F_PER_WF m }.

  Class MonadWF :=
    { Monad_left_unit :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (f:A -> m B) `{! Proper eqv f }
          (a:A) `{! Proper eqv a },
        mbind (mret a) f ~= f a
    ; Monad_right_unit :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (aM:m A) `{! Proper eqv aM },
        mbind aM mret ~= aM
    ; Monad_associativity :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          {C} `{! Eqv C ,! PER_WF C }
          (f:A -> m B) `{! Proper eqv f }
          (g:B -> m C) `{! Proper eqv g }
          (aM:m A) `{! Proper eqv aM },
        mbind (mbind aM f) g ~= mbind aM (fun a => mbind (f a) g)
    ; mret_Proper :>
        forall {A} `{! Eqv A ,! PER_WF A },
        Proper eqv (mret (A:=A))
    ; mbind_Proper :>
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B },
        Proper eqv (mbind (A:=A) (B:=B))
    }.

End MonadWF.
Arguments MonadWF m {_ _}.
Hint Extern 9 (Proper eqv (mret (m:=?m) (A:=?A))) =>
  let H := fresh "H" in
  pose (H:=(mret_Proper (m:=m) (A:=A))) ; apply H
  : typeclass_instances.
Hint Extern 9 (Proper eqv (mbind (m:=?m) (A:=?A) (B:=?B))) =>
  let H := fresh "H" in
  pose (H:=(mbind_Proper (m:=m) (A:=A) (B:=B))) ; apply H
  : typeclass_instances.