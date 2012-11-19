Require Import Data.FunctionPre.

Class Injection T U := { inject : T -> U }.

Class Bijection T U :=
  { bijection_Injection_T_U :> Injection T U
  ; bijection_Injection_U_T :> Injection U T
  }.
Hint Immediate Build_Bijection : typeclass_instances.

Definition from {T U} {B:Bijection T U} : U -> T := inject.
Definition to {T U} {B:Bijection T U} : T -> U := inject.

Instance refl_Injection {T} : Injection T T := { inject := id }.

Class FunctorInjection (T U:Type -> Type) := { finject : forall {A}, T A -> U A }.

Class FunctorBijection T U :=
  { functor_bijection_FunctorInjection_T_U :> FunctorInjection T U
  ; functor_bijection_FunctorInjection_U_T :> FunctorInjection U T
  }.
Hint Immediate Build_FunctorBijection : typeclass_instances.

Definition ffrom {T U} {B:FunctorBijection T U} {A} : U A -> T A := finject.
Definition fto {T U} {B:FunctorBijection T U} {A} : T A -> U A := finject.

Instance refl_FunctorInjection {T} : FunctorInjection T T := { finject := fun _ => id }.