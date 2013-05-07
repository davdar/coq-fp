Require Import FP.CoreData.Function.
Require Import FP.CoreClasses.Setoid.

Import FunctionNotation.
Import ProperNotation.

Class InjectionRespect T U (inj:T->U) R1 R2 :=
  { InjectionRespect_eta :> Proper (R1 ==> R2) inj
  ; InjectionRespect_beta :> Proper (R1 <== R2) inj
  }.

Class InjectionDistribute T U (inj:T->U) (T_op:T->T->T) (U_op:U->U->U) (R:U->U->Prop) :=
  { InjectionDistribute_law :
      forall {t1 t2}, inj (t1 `T_op` t2) `R` (inj t1 `U_op` inj t2)
  }.

Class InjectionInverse T U (to:T->U) (from:U->T) R :=
  { InjectionInverse_inv : forall {x}, R (from (to x)) x }.