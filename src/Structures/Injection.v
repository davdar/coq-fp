Require Import FP.Data.Function.
Require Import FP.Relations.Setoid.

Import FunctionNotation.

Class Injection T U (mor:T -> U) := { inject := mor }.
Instance refl_Injection {T} : Injection T T id := {}.

Class Bijection T U mto mfrom :=
  { bijection_Injection_T_U : Injection T U mto
  ; bijection_Injection_U_T : Injection U T mfrom
  }.
Hint Resolve Build_Bijection : typeclass_instances.
Hint Immediate (@bijection_Injection_T_U _ _) : typeclass_instances.
Hint Immediate (@bijection_Injection_U_T _ _) : typeclass_instances.

Definition to {T U mto mfrom} {B:Bijection T U mto mfrom} : T -> U := mto.
Definition from {T U mto mfrom} {B:Bijection T U mto mfrom} : U -> T := mfrom.

Class InjectionRespect T U mor R1 R2 {Bij:Injection T U mor} :=
  { inject_resp_eta :> Proper (R1 ==> R2) mor
  ; inject_resp_beta :> Proper (R1 <== R2) mor
  }.

Class InjectionInverse T U mfrom mto R :=
  { inject_inverse : forall x, R x (mfrom (mto x))
Class BijectionRespect T U mto mfrom R1 R2 {Bij:Bijection T U mto mfrom} :=
  { bijection_wf_InjectionRespect_T_U : InjectionRespect T U mto R1 R2
  ; bijection_wf_InjectionRespect_U_T : InjectionRespect U T mfrom R2 R1
  ; bijection_rel_from_to : forall x, R1 x (from (to x))
  ; bijection_rel_to_from : forall x, R2 x (to (from x))
  }.
Hint Resolve Build_BijectionRespect : typeclass_instances.
Hint Immediate (@bijection_wf_InjectionRespect_T_U _ _) : typeclass_instances.
Hint Immediate (@bijection_wf_InjectionRespect_U_T _ _) : typeclass_instances.

Section resp.
  Context {A B mto mfrom R1 R2}
          {Bij:Bijection A B mto mfrom}
          {BijWF:BijectionRespect A B mto mfrom R1 R2}.

  Global Instance iso_Injection_from_to : Injection A A (mfrom '.' mto).
    constructor. Qed.
  Global Instance iso_Injection_to_from : Injection B B (mto '.' mfrom).
    constructor. Qed.
  Global Instance iso_InjectionRespect_from_to
      : InjectionRespect A A (mfrom '.' mto) R1 R1.
    constructor ; unfold Proper ; unfold "==>" ; unfold "<==" ; unfold compose ;
      intros.
    repeat (apply inject_resp_eta) ; auto.
    repeat (apply inject_resp_beta in H) ; auto.
    Qed.

  Global Instance iso_InjectionRespect_to_from
      : InjectionRespect B B (mto '.' mfrom) R2 R2.
    constructor ; unfold Proper ; unfold "==>" ; unfold "<==" ; unfold compose ;
      intros.
    repeat (apply inject_resp_eta) ; auto.
    repeat (apply inject_resp_beta in H) ; auto.
    Qed.
End resp.

Class FunctorInjection (T U:Type -> Type) := { finject : forall {A}, T A -> U A }.
Instance refl_FunctorInjection {T} : FunctorInjection T T :=
  { finject := fun _ => id }.

Class FunctorBijection T U :=
  { functor_bijection_FunctorInjection_T_U : FunctorInjection T U
  ; functor_bijection_FunctorInjection_U_T : FunctorInjection U T
  }.
Hint Resolve Build_FunctorBijection : typeclass_instances.
Hint Immediate (@functor_bijection_FunctorInjection_T_U _ _) : typeclass_instances.
Hint Immediate (@functor_bijection_FunctorInjection_U_T _ _) : typeclass_instances.

Definition fto {T U} {B:FunctorBijection T U} {A} : T A -> U A := finject.
Definition ffrom {T U} {B:FunctorBijection T U} {A} : U A -> T A := finject.