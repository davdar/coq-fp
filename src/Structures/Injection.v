Require Import FP.Data.Function.

Class Injection T U := { inject : T -> U }.
Instance refl_Injection {T} : Injection T T := { inject := id }.

Class Bijection T U :=
  { bijection_Injection_T_U : Injection T U
  ; bijection_Injection_U_T : Injection U T
  }.
Hint Resolve Build_Bijection : typeclass_instances.
Hint Immediate (@bijection_Injection_T_U _ _) : typeclass_instances.
Hint Immediate (@bijection_Injection_U_T _ _) : typeclass_instances.

Definition to {T U} {B:Bijection T U} : T -> U := inject.
Definition from {T U} {B:Bijection T U} : U -> T := inject.

Class FunctorInjection (T U:Type -> Type) := { finject : forall {A}, T A -> U A }.
Instance refl_FunctorInjection {T} : FunctorInjection T T := { finject := fun _ => id }.

Class FunctorBijection T U :=
  { functor_bijection_FunctorInjection_T_U : FunctorInjection T U
  ; functor_bijection_FunctorInjection_U_T : FunctorInjection U T
  }.
Hint Resolve Build_FunctorBijection : typeclass_instances.
Hint Immediate (@functor_bijection_FunctorInjection_T_U _ _) : typeclass_instances.
Hint Immediate (@functor_bijection_FunctorInjection_U_T _ _) : typeclass_instances.

Definition fto {T U} {B:FunctorBijection T U} {A} : T A -> U A := finject.
Definition ffrom {T U} {B:FunctorBijection T U} {A} : U A -> T A := finject.