Require Import FP.Data.Function.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.EqvRel.
Require Import FP.Relations.Setoid.

Import ProperNotation.

Class MPipe (m:Type->Type) :=
  { mpipe : forall {A B C}, (A -> m B) -> (B -> m C) -> A -> m C }.

Section MPipe.
  Context {m} {MPipe_:MPipe m}.

  Definition mcompose {A B C} : (B -> m C) -> (A -> m B) -> A -> m C := flip mpipe.
End MPipe.

Module KleisliNotation.
  Infix ">=>" := mpipe (at level 53, right associativity).
  Infix "<=<" := mcompose (at level 53, right associativity).
End KleisliNotation.

Section KleisliWF.
  Variable (m:Type->Type).
  Context {FUnit_:FUnit m} {MPipe_:MPipe m}.
  Variable (EqvEnv_:EqvEnv).
  Context {RPromote:forall {A} {aER:EqvRel A}, EqvRel (m A)}.

  Class KleisliWF :=
    { mpipe_left_unit :
        forall
          {A} {aER:EqvRel A}
          {B} {bER:EqvRel B}
          (f:A -> m B) (f':A -> m B) {fP:(env_R ==> env_R) f f'}
          (a:A) (a':A) {aP:env_R a a'},
            env_R
            (mpipe funit f a)
            (f' a')
    ; mpipe_right_unit :
        forall
          {A} {aER:EqvRel A}
          {B} {bER:EqvRel B}
          (f:A -> m B) (f':A -> m B) {fP:(env_R ==> env_R) f f'}
          (a:A) (a':A) {aP:env_R a a'},
            env_R
            (mpipe f funit a)
            (f' a')
    ; mpipe_associativity :
        forall
          {A} {aER:EqvRel A}
          {B} {bER:EqvRel B}
          {C} {cER:EqvRel C}
          {D} {dER:EqvRel D}
          (f:A -> m B) (f':A -> m B) {fP:(env_R ==> env_R) f f'}
          (g:B -> m C) (g':B -> m C) {gP:(env_R ==> env_R) g g'}
          (h:C -> m D) (h':C -> m D) {hP:(env_R ==> env_R) h h'}
          (a:A) (a':A) {aP:env_R a a'},
            env_R
            (mpipe (mpipe f g) h a)
            (mpipe f (mpipe g h) a)
    }.
End KleisliWF.
