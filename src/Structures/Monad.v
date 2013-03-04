Require Import FP.Structures.FUnit.
Require Import FP.Structures.EqvRel.
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
    bind aM (funit '.' f).
  Definition bind_fapply {A B} (fM:m (A -> B)) (aM:m A) : m B :=
    bind fM (fun f => bind aM (fun a => funit (f a))).
  Definition bind_ftimes {A B} (aM:m A) (bM:m B) : m (A*B) :=
    bind aM (fun a => bind bM (fun b => funit (a,b))).
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
  Variable (m:Type->Type).
  Context {FUnit_:FUnit m} {MBind_:MBind m}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {E_R_m:forall {A} {aER:PE_R A}, PE_R (m A)}.

  Class MonadWF :=
    { bind_left_unit :
        forall
          {A} {aER:E_R A}
          {B} {bER:E_R B}
          (f:A -> m B) {fP:Proper PE_eqv f}
          (a:A) {aP:Proper PE_eqv a},
            PE_eqv
            (bind (ret a) f)
            (f a)
    ; bind_right_unit :
        forall
          {A} {aER:E_R A}
          (aM:m A) {aMP:Proper PE_eqv aM},
            PE_eqv
            (bind aM ret)
            aM
    ; bind_associativity :
        forall
          {A} {aER:E_R A}
          {B} {bER:E_R B}
          {C} {cER:E_R C}
          (f:A -> m B) {fP:Proper PE_eqv f}
          (g:B -> m C) {gP:Proper PE_eqv g}
          (aM:m A) {aP:Proper PE_eqv aM},
          PE_eqv
          (bind (bind aM f) g)
          (bind aM (fun a => bind (f a) g))
    ; bind_respect :>
        forall
          {A} {aER:E_R A}
          {B} {bER:E_R B},
            Proper PE_eqv (bind (A:=A) (B:=B))
    }.
End MonadWF.