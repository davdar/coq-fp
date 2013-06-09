Require Import FP.Data.Error.
Require Import FP.Classes.
Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.DerivingEverything.
Require Import FP.Data.Identity.

Import CoreDataNotation.
Import CoreClassesNotation.
Import ClassesNotation.

Inductive error_t E m A := ErrorT { run_error_t : m (error E A) }.
Arguments ErrorT {E m A} _.
Arguments run_error_t {E m A} _.

Definition error_b E := error_t E identity.

Section error_t_Bijection.
  Context {E:Type} {m:Type -> Type} {A:Type}.

  Global Instance IR_run_error_t_eq
    : InjectionRespect (error_t E m A) (m (error E A)) run_error_t eq eq.
  Proof.
    constructor ; [congruence|].
    unfold Proper,"<==" ; intros ; destruct x,y ; simpl in * ; congruence.
  Qed.

  Global Instance II_ErrorT_eq
    : InjectionInverse (m (error E A)) (error_t E m A) ErrorT run_error_t eq.
  Proof.
    constructor ; auto.
  Qed.
End error_t_Bijection.

Module error_t_DE_Arg <: DE_IdxTransformer_Arg.
  Definition T := error_t.
  Definition U E m A := m (error E A):Type.
  Definition to : forall {E m A}, T E m A -> U E m A := @run_error_t.
  Definition from : forall {E m A}, U E m A -> T E m A := @ErrorT.
  Definition IR_to {E m A} : InjectionRespect (T E m A) (U E m A) to eq eq := _.
  Definition II_from {E m A} : InjectionInverse (U E m A) (T E m A) from to eq := _.
  Definition _DE_IdxTransformerI : DE_IdxTransformerI' U.
  Proof. unfold U ; econstructor ; econstructor ; eauto with typeclass_instances. Defined.
End error_t_DE_Arg.
Module error_t_DE := DE_IdxTransformer error_t_DE_Arg.
Import error_t_DE.

Section Proper.
  Context {E m A} `{! Eqv  E ,! F_Eqv m ,! Eqv A }.
  Global Instance ErrorT_Proper : Proper eqv (@ErrorT E m A).
  Proof.
    unfold Proper.
    logical_eqv_intro.
    unfold eqv ; simpl ; auto.
  Qed.
  Global Instance run_error_t_Proper : Proper eqv (@run_error_t E m A).
  Proof.
    unfold Proper.
    logical_eqv_intro.
    destruct x,y ; simpl.
    apply InjectionRespect_beta ; auto.
  Qed.
End Proper.
Hint Extern 9 (Proper eqv (ErrorT (E:=?E) (m:=?m) (A:=?A))) =>
  let H := fresh "H" in
  pose (H:=(ErrorT_Proper (E:=E) (m:=m) (A:=A))) ; apply H
  : typeclass_instances.
Hint Extern 9 (Proper eqv (run_error_t (E:=?E) (m:=?m) (A:=?A))) =>
  let H := fresh "H" in
  pose (H:=(run_error_t_Proper (E:=E) (m:=m) (A:=A))) ; apply H
  : typeclass_instances.

Section Monad.
  Context {E:Type} {m} `{! Monad m }.

  Definition error_t_mret {A} (a:A) : error_t E m A := ErrorT $ mret $ Success a.
  Arguments error_t_mret {A} a /.

  Definition error_t_mbind {A B} (aMM:error_t E m A) (k:A -> error_t E m B) : error_t E m B :=
    ErrorT begin
      aM <- run_error_t aMM ;;
      match aM with
      | Failure e => mret $ Failure e
      | Success a => run_error_t $ k a
      end
    end.
  Arguments error_t_mbind {A B} aMM k /.
  Global Instance error_t_Monad : Monad (error_t E m) :=
    { mret := @error_t_mret
    ; mbind := @error_t_mbind
    }.

  Section error_t_MonadWF.
    Context `{! Eqv E ,! PER_WF E ,! F_Eqv m ,! F_PER_WF m ,! MonadWF m }.

    Global Instance error_t_MonadWF : MonadWF (error_t E m).
    Proof.
      constructor ; intros.
      - apply InjectionRespect_beta ; simpl.
        rewrite Monad_left_unit ; repeat (logical_eqv ; repeat fold_error).
      - apply InjectionRespect_beta ; simpl.
        transitivity (run_error_t aM >>= mret).
        + logical_eqv.
          destruct x,y ; inversion H ; subst ; clear H ; logical_eqv.
        + rewrite Monad_right_unit ; logical_eqv.
      - apply InjectionRespect_beta ; simpl.
        rewrite Monad_associativity ; repeat (logical_eqv ; repeat fold_error).
        destruct x,y ; inversion H ; subst ; clear H ; repeat (logical_eqv ; repeat fold_error) ; simpl.
        rewrite Monad_left_unit ; repeat (logical_eqv ; repeat fold_error) ; simpl.
        repeat (logical_eqv ; repeat fold_error).
      - unfold Proper ; logical_eqv_intro.
        apply InjectionRespect_beta ; simpl.
        repeat (logical_eqv ; repeat fold_error).
      - unfold Proper ; logical_eqv_intro.
        apply InjectionRespect_beta ; simpl.
        repeat (logical_eqv ; repeat fold_error).
    Qed.
  End error_t_MonadWF.
End Monad.

Section MonadCatch.
  Context {E:Type} {m} `{! Monad m }.
  Definition error_t_mthrow {A} (e:E) : error_t E m A := ErrorT $ mret $ Failure e.
  Arguments error_t_mthrow {A} e /.
  Definition error_t_mcatch {A} (aM:error_t E m A) (k:E -> error_t E m A) : error_t E m A :=
    ErrorT begin
      am <- run_error_t aM ;;
      match am with
      | Success a => mret $ Success a
      | Failure e => run_error_t $ k e
      end
    end.
  Arguments error_t_mcatch {A} aM k /.
  Global Instance error_t_MonadCatch : MonadCatch E (error_t E m) :=
    { mthrow := @error_t_mthrow
    ; mcatch := @error_t_mcatch
    }.

  Section error_t_MonadCatchWF.
    Context `{! Eqv E ,! PER_WF E ,! F_Eqv m ,! F_PER_WF m ,! MonadWF m }.

    Global Instance error_t_MonadCatchWF : MonadCatchWF E (error_t E m).
    Proof.
      constructor ; intros ; unfold mcatch,mthrow ; simpl.
      - apply InjectionRespect_beta ; simpl.
        rewrite Monad_left_unit ; repeat (logical_eqv ; repeat fold_error).
      - apply InjectionRespect_beta ; simpl.
        rewrite Monad_left_unit ; repeat (logical_eqv ; repeat fold_error).
      - apply InjectionRespect_beta ; simpl.
        rewrite Monad_left_unit ; repeat (logical_eqv ; repeat fold_error).
      - unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
      - unfold Proper ; logical_eqv_intro ; simpl ; repeat (logical_eqv ; repeat fold_error).
    Qed.
  End error_t_MonadCatchWF.
End MonadCatch.