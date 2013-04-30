Require Import FP.Structures.FUnit.
Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.Eqv.
Require Import FP.Relations.Setoid.
Require Import FP.Data.Function.

Import ProperNotation.
Import FunctionNotation.

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
  Context {m} {FUnit_:FUnit m} {MBind_:MBind m}.

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
Arguments ret {m FUnit_ A} _ /.
Arguments extend {m MBind_ A B} _ _ /.
Arguments bind_mpipe {m MBind_ A B C} f g a /.
Arguments bind_mjoin {m MBind_ A} aMM /.
Arguments bind_fmap {m FUnit_ MBind_ A B} f aM /.
Arguments bind_fapply {m FUnit_ MBind_ A B} fM aM /.
Arguments bind_ftimes {m FUnit_ MBind_ A B} aM bM /.

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
  Context {FUnit_:FUnit m} {MBind_:MBind m}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {PE_R_t:forall {A} {aER:Px (env_PER A)}, Px (env_PER (m A))}.
  Context {PE_R_t' :
    forall {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)},
    Px (env_PER_WF (m A))}.

  Class MonadWF :=
    { bind_left_unit :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (f:A -> m B) {fP:Proper env_eqv f}
          (a:A) {aP:Proper env_eqv a},
        env_eqv
        (bind (ret a) f)
        (f a)
    ; bind_right_unit :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          (aM:m A) {aMP:Proper env_eqv aM},
        env_eqv
        (bind aM ret)
        aM
    ; bind_associativity :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          {C} {cER:Px (env_PER C)} {cER':Px (env_PER_WF C)}
          (f:A -> m B) {fP:Proper env_eqv f}
          (g:B -> m C) {gP:Proper env_eqv g}
          (aM:m A) {aP:Proper env_eqv aM},
        env_eqv
        (bind (bind aM f) g)
        (bind aM (fun a => bind (f a) g))
    ; bind_respect :>
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)},
        Proper env_eqv (bind (A:=A) (B:=B))
    }.
End MonadWF.
Arguments MonadWF m {_ _ _ _ _}.
Hint Extern 9 (Proper env_eqv bind) => apply bind_respect : typeclass_instances.

Section EqvEnv_eqv.
  Local Instance EqvEnv_ : EqvEnv := eqv_EqvEnv.
  Local Instance EqvEnvLogical_ : EqvEnvLogical := eqv_EqvEnvLogical.
  Context {m:Type->Type}.
  Context {FUnit_:FUnit m} {MBind_:MBind m}.
  Context {PE_R_t:forall {A} {aER:Eqv A}, Eqv (m A)}.
  Context {PE_R_t' :
    forall {A} {aER:Eqv A} {aER':Eqv_PE_WF A},
    Eqv_PE_WF (m A)}.
  Context {MonadWF_:MonadWF m}.

  Definition bind_left_unit_eqv :
      forall
        {A} {aER:Eqv A} {aER':Eqv_PE_WF A}
        {B} {bER:Eqv B} {bER':Eqv_PE_WF B}
        (f:A -> m B) {fP:Proper eqv f}
        (a:A) {aP:Proper eqv a},
      eqv
      (bind (ret a) f)
      (f a).
  Proof.
    intros.
    pose (@bind_left_unit _ _ _ _ _ _ _).
    eapply e ; auto.
  Qed.

  Definition bind_right_unit_eqv :
    forall
      {A} {aER:Eqv A} {aER':Eqv_PE_WF A}
      (aM:m A) {aMP:Proper eqv aM},
    eqv
    (bind aM ret)
    aM.
  Proof.
    intros.
    pose (@bind_right_unit _ _ _ _ _ _ _).
    eapply e ; auto.
  Qed.

  Definition bind_associativity_eqv :
    forall
      {A} {aER:Eqv A} {aER':Eqv_PE_WF A}
      {B} {bER:Eqv B} {bER':Eqv_PE_WF B}
      {C} {cER:Eqv C} {cER':Eqv_PE_WF C}
      (f:A -> m B) {fP:Proper eqv f}
      (g:B -> m C) {gP:Proper eqv g}
      (aM:m A) {aP:Proper eqv aM},
    eqv
    (bind (bind aM f) g)
    (bind aM (fun a => bind (f a) g)).
  Proof.
    intros.
    pose (@bind_associativity _ _ _ _ _ _ _).
    eapply e ; auto.
  Qed.

  Global Instance bind_respect_eqv :
    forall
      {A} {aER:Eqv A} {aER':Eqv_PE_WF A}
      {B} {bER:Eqv B} {bER':Eqv_PE_WF B},
    Proper eqv (bind (A:=A) (B:=B)).
  Proof.
    intros.
    pose (@bind_respect _ _ _ _ _ _ _).
    eapply p ; auto.
  Qed.
End EqvEnv_eqv.