Require Import FP.Structures.Proxy.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.Feq.
Require Import FP.Structures.EqDec.
Require Import FP.Data.Function.
Require Import FP.Relations.Setoid.

Import ProperNotation.

Class Category (t:Type -> Type -> Type) :=
  { cid : forall {A}, t A A
  ; ccompose : forall {A B C}, t B C -> t A B -> t A C
  }.
Arguments cid {t Category A} : simpl never.
Arguments ccompose {t Category A B C} _ _ : simpl never.

Section CategoryWF.
  Context {t:Type->Type->Type}.
  Context {Category_:Category t}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {tPER :
    forall
      {A} {aER:Px (env_PER A)}
      {B} {bER:Px (env_PER B)},
    Px (env_PER (t A B))}.
  Context {tPER' :
    forall
      {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
      {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)},
    Px (env_PER_WF (t A B))}.

  Class CategoryWF :=
    { category_left_unit :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (f:t A B) {fP:Proper env_eqv f},
            env_eqv
            (ccompose cid f)
            f
    ; category_right_unit :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (f:t A B) {fP:Proper env_eqv f},
            env_eqv
            (ccompose f cid)
            f
    ; category_associativity :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          {C} {cER:Px (env_PER C)} {cER':Px (env_PER_WF C)}
          {D} {dER:Px (env_PER D)} {dER':Px (env_PER_WF D)}
          (f:t A B) {fP:Proper env_eqv f}
          (g:t B C) {gP:Proper env_eqv g}
          (h:t C D) {hP:Proper env_eqv h},
            env_eqv
            (ccompose (ccompose h g) f)
            (ccompose h (ccompose g f))
    }.
End CategoryWF.
Arguments CategoryWF t {_ _ _}.

Module CategoryNotation.
  Infix "<.>" := ccompose (at level 45, right associativity).
End CategoryNotation.