Require Import FP.Structures.FUnit.
Require Import FP.Structures.Functor.
Require Import FP.Structures.EqvRel.

Class MJoin (m:Type->Type) :=
  { mjoin : forall {A}, m (m A) -> m A }.

Section MJoinWF.
  Variable (m:Type->Type).
  Context {FUnit_:FUnit m} {FMap_:FMap m} {MJoin_:MJoin m}.
  Variable (EqvEnv_:EqvEnv).
  Context {RPromote:forall {A} {aER:EqvRel A}, EqvRel (m A)}.

  Class MJoinWF :=
    { mjoin_left_unit :
        forall
          {A} {aER:EqvRel A}
          (aM:m A) (aM':m A) {aP:env_R aM aM'},
          env_R
          (mjoin (funit aM))
          aM
    }.
End MJoinWF.