Require Import FP.CoreClasses.
Require Import FP.CoreData.
Require Import FP.Categories.Pointed.
Require Import FP.Categories.Functor.
Require Import FP.Categories.Applicative.

Import ProperNotation.
Import FunctionNotation.
Import EqvNotation.

Class MBind (m:Type->Type) :=
  { bind : forall {A B}, m A -> (A -> m B) -> m B }.

Class Monad (m:Type->Type) :=
  { Monad_FUnit : FUnit m
  ; Monad_MBind : MBind m
  }.
Hint Resolve Build_Monad : typeclass_instances.
Hint Immediate Monad_FUnit : typeclass_instances.
Hint Immediate Monad_MBind : typeclass_instances.

Section Monad.
  Context {m} `{! FUnit m ,! MBind m}.

  Definition ret {A} : A -> m A := funit.

  Definition extend {A B} : (A -> m B) -> (m A -> m B) := flip bind.
  Definition seq {A B} (aM:m A) (bM:m B) : m B := bind aM (const bM).

  Definition bind_mpipe {A B C} (f:A -> m B) (g:B -> m C) (a:A) : m C :=
    bind (f a) g.
  Definition bind_mjoin {A} (aMM:m (m A)) : m A :=
    bind aMM id.
  Definition bind_fmap {A B} (f:A -> B) (aM:m A) : m B :=
    bind aM (ret '.' f).
  Definition bind_fapply {A B} (fM:m (A -> B)) (aM:m A) : m B :=
    bind fM (fun f => bind aM (fun a => ret (f a))).
  Definition bind_ftimes {A B} (aM:m A) (bM:m B) : m (A*B) :=
    bind aM (fun a => bind bM (fun b => ret (a,b))).
End Monad.
Arguments ret {m _ A} _ /.
Arguments extend {m _ A B} _ _ /.
Arguments bind_mpipe {m _ A B C} f g a /.
Arguments bind_mjoin {m _ A} aMM /.
Arguments bind_fmap {m _ _ A B} f aM /.
Arguments bind_fapply {m _ _ A B} fM aM /.
Arguments bind_ftimes {m _ _ A B} aM bM /.

Module MonadNotation.
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity).

  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).

  Infix ">>=" := bind (at level 50, left associativity).
  Infix "=<<" := extend (at level 51, right associativity).
  Infix ">>" := seq (at level 50, left associativity).
End MonadNotation.

Section MonadWF.
  Context {m:Type->Type}.
  Context `{! FUnit m ,! MBind m ,! F_Eqv m ,! F_PER_WF m }.

  Class MonadWF :=
    { bind_left_unit :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (f:A -> m B) `{! Proper eqv f }
          (a:A) `{! Proper eqv a },
        bind (ret a) f ~= f a
    ; bind_right_unit :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (aM:m A) `{! Proper eqv aM },
        bind aM ret ~= aM
    ; bind_associativity :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          {C} `{! Eqv C ,! PER_WF C }
          (f:A -> m B) `{! Proper eqv f }
          (g:B -> m C) `{! Proper eqv g }
          (aM:m A) `{! Proper eqv aM },
        bind (bind aM f) g ~= bind aM (fun a => bind (f a) g)
    ; bind_respect :>
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B },
        Proper eqv (bind (A:=A) (B:=B))
    }.

End MonadWF.
Arguments MonadWF m {_ _ _}.
Hint Extern 9 (Proper eqv bind) => apply bind_respect : typeclass_instances.

Section Deriving_FApply_MBind.
  Context {m} `{! FUnit m ,! MBind m }.
  Definition deriving_FApply_MBind {A} {B} : m (A -> B) -> m A -> m B := bind_fapply.
  Definition Deriving_FApply_MBind : FApply m := {| fapply := @deriving_FApply_MBind |}.
End Deriving_FApply_MBind.

Section Deriving_ApplicativeWF_MonadWF.
  Context {m} `{! FUnit m ,! FApply m ,! MBind m
               ,! F_Eqv m ,! F_PER_WF m
               ,! PointedWF m ,! MonadWF m
               }.

  Global Instance bind_fapply_respect
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (bind_fapply (A:=A) (B:=B)).
  Proof.
    unfold bind_fapply ; logical_eqv.
  Qed.

  Class MonadRespApplicative :=
    { bind_respect_fapply :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (fM:m (A -> B)) `{! Proper eqv fM }
          (aM:m A) `{! Proper eqv aM },
        fapply fM aM ~= bind_fapply fM aM
    }.

  Context `{! MonadRespApplicative }.

  Local Instance fapply_respect'
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (fapply (A:=A) (B:=B)).
  Proof.
    unfold Proper ; logical_eqv_intro.
    repeat rewrite bind_respect_fapply ; logical_eqv.
  Qed.
  Local Hint Extern 9 (Proper eqv fapply) => apply fapply_respect' : typeclass_instances.

  Definition Deriving_ApplicativeWF_MonadWF : ApplicativeWF m.
  Proof.
    constructor ; intros.
    - rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_left_unit ; logical_eqv ; simpl.
      apply bind_right_unit ; auto.
    - rewrite bind_respect_fapply ; logical_eqv.
      rewrite bind_respect_fapply ; logical_eqv.
      rewrite bind_respect_fapply ; logical_eqv.
      rewrite bind_respect_fapply ; logical_eqv.
      rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv ; simpl.
      logical_eqv.
    - rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv.
    - rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv ; simpl.
      logical_eqv.
    - apply fapply_respect'.
  Qed.
End Deriving_ApplicativeWF_MonadWF.