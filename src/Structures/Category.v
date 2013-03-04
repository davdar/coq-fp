Require Import FP.Structures.Proxy.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.EqvRel.
Require Import FP.Structures.EqDec.
Require Import FP.Data.Function.
Require Import FP.Relations.Setoid.

Import ProperNotation.

Class Category (t:Type -> Type -> Type) :=
  { cid : forall {A}, t A A
  ; ccompose : forall {A B C}, t B C -> t A B -> t A C
  }.

Section CategoryWF.
  Context {t:Type->Type->Type}.
  Context {Category_:Category t}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {tPER:forall {A} {aER:PE_R A} {B} {bER:PE_R B}, PE_R (t A B)}.

  Class CategoryWF :=
    { category_left_unit :
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B}
          (f:t A B) {fP:Proper PE_eqv f},
            PE_eqv
            (ccompose cid f)
            f
    ; category_right_unit :
        forall
          {A} {aER:E_R A}
          {B} {bER:E_R B}
          (f:t A B) {fP:Proper PE_eqv f},
            PE_eqv
            (ccompose f cid)
            f
    ; category_associativity :
        forall
          {A} {aER:E_R A}
          {B} {bER:E_R B}
          {C} {cER:E_R C}
          {D} {dER:E_R D}
          (f:t A B) {fP:Proper PE_eqv f}
          (g:t B C) {gP:Proper PE_eqv g}
          (h:t C D) {hP:Proper PE_eqv h},
            PE_eqv
            (ccompose (ccompose h g) f)
            (ccompose h (ccompose g f))
    }.
End CategoryWF.
Arguments CategoryWF t {_ _ _ _}.

Section CategoryWF_Eq.
  Local Instance eqv_env : EqvEnv := eq_EqvEnv.
  Local Instance eqv_env_wf : EqvEnvWF := eq_EqvEnvWF.
  Context {t:Type->Type->Type}.
  Context {Category:Category t}.
  Context {CategoryWF:CategoryWF t (EqvEnv_:=eq_EqvEnv)}.
  Definition category_right_unit_eq
    {A B} (f:t A B) : eq (ccompose f cid) f :=
      category_right_unit f f (reflexivity f).
  Definition category_left_unit_eq
    {A} {B} (f:t A B) : eq (ccompose cid f) f :=
      category_left_unit f f (reflexivity f).
  Definition category_associativity_eq
    {A} {B} {C} {D} (f:t A B) (g:t B C) (h:t C D) :
      eq (ccompose (ccompose h g) f) (ccompose h (ccompose g f)) :=
    category_associativity
      f f (reflexivity f)
      g g (reflexivity g)
      h h (reflexivity h).
End CategoryWF_Eq.

Module CategoryNotation.
  Infix "<.>" := ccompose (at level 45, right associativity).
End CategoryNotation.