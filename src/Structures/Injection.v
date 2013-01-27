Require Import FP.Data.Function.
Require Import FP.Relations.Function.
Require Import FP.Relations.Setoid.

Import FunctionNotation.
Import MorphismNotation.

Class InjectionRespect T U (inj:T->U) R1 R2 :=
  { InjectionRespect_eta :> Proper (R1 ==> R2) inj
  ; InjectionRespect_beta :> Proper (R1 <== R2) inj
  }.

Class InjectionDistribute T U
      (inj:T->U) (T_op:T -> T -> T) (U_op:U -> U -> U) (R:U -> U -> Prop) :=
  { InjectionDistribute_law :
      forall t1 t2, inj (t1 `T_op` t2) `R` (inj t1 `U_op` inj t2)
  }.

Class InjectionInverse T U (to:T->U) (from:U->T) R :=
  { InjectionInverse_inv : forall x, R x (from (to x))
  }.

Class HasInjection T U := { inject : T -> U }.
Arguments inject {T U HasInjection} _ : simpl never.

Class BijectionRespect T U to from R1 R2 :=
  { BijectionRespect_to : InjectionRespect T U to R1 R2
  ; BijectionRespect_from : InjectionRespect U T from R2 R1
  }.
Hint Resolve Build_BijectionRespect : typeclass_instances.
Hint Immediate (@BijectionRespect_to _ _) : typeclass_instances.
Hint Immediate (@BijectionRespect_from _ _) : typeclass_instances.

Class BijectionCorrect T U to from R1 R2 :=
  { BijectionCorrect_to : InjectionInverse T U to from R1
  ; BijectionCorrect_from : InjectionInverse U T from to R2
  }.

Class HasBijection T U :=
  { HasBijection_to : HasInjection T U
  ; HasBijection_from : HasInjection U T
  }.
Hint Resolve Build_HasBijection : typeclass_instances.
Hint Immediate HasBijection_to : typeclass_instances.
Hint Immediate HasBijection_from : typeclass_instances.


Class FunctorInjection (t u:Type -> Type) (finj:forall {A}, t A -> u A) := {}.
Class FunctorBijection t u to from :=
  { FunctorBijection_to : FunctorInjection t u to
  ; FunctorBijection_from : FunctorInjection u t from
  }.
Hint Resolve Build_FunctorBijection : typeclass_instances.
Hint Immediate (@FunctorBijection_to _ _) : typeclass_instances.
Hint Immediate (@FunctorBijection_from _ _) : typeclass_instances.

Class HasFunctorInjection (t u:Type -> Type) := { finject : forall {A}, t A -> u A }.
Instance FunctorInjection_HasFunctorInjection
    t u finj {FInj:FunctorInjection t u finj} : HasFunctorInjection t u :=
  { finject := finj }.

Class HasFunctorBijection (t u:Type -> Type) :=
  { HasFunctorBijection_to : HasFunctorInjection t u
  ; HasFunctorBijection_from : HasFunctorInjection u t
  }.
Hint Resolve Build_HasFunctorBijection : typeclass_instances.
Hint Immediate HasFunctorBijection_to : typeclass_instances.
Hint Immediate HasFunctorBijection_from : typeclass_instances.

Section HasFunctorBijection.
  Context {t u} {T_U_FBij:HasFunctorBijection t u}.

  Definition fto {A} : t A -> u A := finject.
  Definition ffrom {A} : u A -> t A := finject.
End HasFunctorBijection.