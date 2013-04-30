Require Import FP.Data.Function.
Require Import FP.Data.String.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.Monad.
Require Import FP.Relations.Setoid.

Import FunctionNotation.
Import ProperNotation.

Class MError (E:Type) (m:Type -> Type) : Type :=
  { throw : forall {A}, E -> m A
  ; catch : forall {A}, m A -> (E -> m A) -> m A
  }.

Section MError.
  Context {m E} {MError_:MError E m}.
  Context {e_HasInjection : HasInjection string E}.

  Definition throw_msg {A} : string -> m A := throw '.' inject.

  Definition catch_with {A} : (E -> m A) -> m A -> m A := flip catch.
  Definition choice {A} (x:m A) (y:m A) : m A :=
    catch x (const y).
End MError.

Section MonadErrorWF.
  Context (E:Type) (m:Type->Type).
  Context {Monad_:Monad m} {MError_:MError E m}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {PE_R_E:Px (env_PER E)}.
  Context {PE_R_E':Px (env_PER_WF E)}.
  Context {PE_R_t:forall {A} {aER:Px (env_PER A)}, Px (env_PER (m A))}.
  Context {PE_R_t' :
    forall {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)},
    Px (env_PER_WF (m A))}.


  Class MonadErrorWF :=
    { throw_left_zero :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (e:E) (eP:Proper env_eqv e)
          (k:A -> m B),
            env_eqv
            (bind (throw e) k)
            (throw e)
    ; catch_of_throw :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          (e:E) (eER:Proper env_eqv e)
          (f:E -> m A) (fP:Proper env_eqv f),
            env_eqv
            (catch (throw e) f)
            (f e)
    ; catch_of_return :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          (a:A) (aP:Proper env_eqv a)
          (f:E -> m A),
            env_eqv
            (catch (ret a) f)
            (ret a)
    ; catch_associativity :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          (aM:m A) (aMP:Proper env_eqv aM)
          (f:E -> m A) (fP:Proper env_eqv f)
          (g:E -> m A) (gP:Proper env_eqv g),
            env_eqv
            (catch (catch aM f) g)
            (catch aM (fun a => catch (f a) g))
    }.
End MonadErrorWF.

  
(*
Section MonadError.
  Context {m E} {Monad:Monad m} {MonadError:MonadError E m}.


  Section choice_laws.
    Variable P:Type->Type.
    Variable R:forall T (p:Proxy2 P T), T -> T -> Prop.
    Arguments R {T p} _ _.
    Variable PWF:Type->Type.
    Variable RWF:forall T (p:Proxy2 P T) (pwf:Proxy2 PWF T), Equivalence R.
    Arguments RWF {T p pwf}.
    Context {eP:Proxy2 P E} {ePWF:Proxy2 PWF E}.

    Context {MonadWF:MonadWF m P (@R) PWF}.
    Context {MonadErrorWF:MonadErrorWF m E P (@R) PWF}.

    Definition choice_throw_left_id :
      forall
        {A} {aP:Proxy2 P A}      {aPWF:Proxy2 PWF A}
            {aMP:Proxy2 P (m A)} {aMPWF:Proxy2 PWF (m A)}
        (e:E) (aM:m A),
          (throw e `choice` aM) `R` aM.
    Proof.
      intros.
      unfold choice ; simpl.
      rewrite catch_of_throw ; eauto with typeclass_instances.
      unfold const.
      reflexivity.
    Qed.

    Definition choice_associativity :
      forall
        {A} {aP:Proxy2 P A}      {aPWF:Proxy2 PWF A}
            {aMP:Proxy2 P (m A)} {aMPWF:Proxy2 PWF (m A)}
        (e:E) (aM:m A) (bM:m A) (cM:m A),
          ((aM `choice` bM) `choice` cM) `R` (aM `choice` (bM `choice` cM)).
    Proof.
      intros.
      unfold choice ; simpl.
      rewrite catch_associativity ; eauto with typeclass_instances.
      reflexivity.
    Qed.
  End choice_laws.

End MonadError.

Module MonadErrorNotation.
  Infix "<|>" := choice (at level 48, left associativity).
End MonadErrorNotation.

Section iso_MonadError.
  Variable n:Type -> Type.
  Context {m} {B:HasFunctorBijection m n} {E} {nME:MonadError E n}.
  Definition iso_MonadError_throw {A} : E -> m A := ffrom '.' throw.
  Definition iso_MonadError_catch {A} (aM:m A) (h:E -> m A) : m A :=
    ffrom $ catch (fto aM) (fto '.' h).
  Definition iso_MonadError : MonadError E m :=
    {| throw := @iso_MonadError_throw
     ; catch := @iso_MonadError_catch
    |}.
End iso_MonadError.
*)