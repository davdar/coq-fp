Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Categories.Pointed.
Require Import FP.Categories.Functor.

Import FunctionNotation.
Import ProperNotation.
Import EqvNotation.

Class FApply t :=
  { fapply : forall {A B}, t (A -> B) -> t A -> t B }.

Class Applicative t : Type :=
  { Applicative_FUnit : FUnit t
  ; Applicative_FApply : FApply t
  }.
Hint Resolve Build_Applicative : typeclass_instances.
Hint Immediate Applicative_FUnit : typeclass_instances.
Hint Immediate Applicative_FApply : typeclass_instances.

Section FApply.
  Context {t} `{! FUnit t ,! FApply t}.

  Definition fapply_fmap {A B} : (A -> B) -> t A -> t B :=
    fapply '.' funit.
  Definition fapply_ftimes {A B} (aT:t A) (bT:t B) : t (A*B) :=
    fapply (fapply (funit pair) aT) bT.
End FApply.
Arguments fapply_fmap {t _ _ A B} _ _ / . 
Arguments fapply_ftimes {t _ _ A B} _ _ / .

Module ApplicativeNotation.
  Infix "<@>" := fapply (at level 46, left associativity).
End ApplicativeNotation.

Section ApplicativeWF.
  Context {t} `{! FUnit t ,! FApply t ,! F_Eqv t ,! F_PER_WF t }.

  Class ApplicativeWF :=
    { fapply_unit :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (aT:t A) `{! Proper eqv aT },
        fapply (funit id) aT ~= aT
    ; fapply_composition :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          {C} `{! Eqv C ,! PER_WF C }
          (fT:t (A -> B)) `{! Proper eqv fT}
          (gT:t (B -> C)) `{! Proper eqv gT}
          (aT:t A) `{! Proper eqv aT },
        fapply gT (fapply fT aT)
        ~= fapply (fapply (fapply (funit compose) gT) fT) aT
    ; fapply_homomorphism :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (f:A -> B) `{! Proper eqv f }
          (a:A) `{! Proper eqv a },
        fapply (funit f) (funit a) ~= funit (f a)
    (* is this derivable? necessary? *)
    ; fapply_interchange :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (fT:t (A -> B)) `{! Proper eqv fT }
          (a:A) `{! Proper eqv a },
        fapply fT (funit a) ~= fapply (funit (apply_to a)) fT
    ; fapply_respect :>
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B },
        Proper eqv (fapply (A:=A) (B:=B))
    }.
End ApplicativeWF.
Arguments ApplicativeWF t {_ _ _}. 
Hint Extern 9 (Proper eqv fapply) => apply fapply_respect : typeclass_instances.

Section Deriving_FMap_FApply.
  Context {t} `{! FUnit t ,! FApply t}.
  Definition deriving_FMap_FApply {A} {B} : (A -> B) -> t A -> t B := fapply_fmap.
  Definition Deriving_FMap_FApply : FMap t :=
    {| fmap := @deriving_FMap_FApply |}.
End Deriving_FMap_FApply.

Section Deriving_FunctorWF_ApplicativeWF.
  Context {t} `{! FUnit t ,! FMap t ,! FApply t
               ,! F_Eqv t ,! F_PER_WF t
               ,! PointedWF t ,! ApplicativeWF t
               }.

  Global Instance fapply_fmap_respect
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (fapply_fmap (A:=A) (B:=B)).
  Proof.
    unfold fapply_fmap ; logical_eqv.
  Qed.

  Class ApplicativeRespectsFunctor :=
    { fapply_respect_fmap :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (f:A -> B) `{! Proper eqv f }
          (aT:t A) `{! Proper eqv aT },
        fmap f aT ~= fapply_fmap f aT
    }.

  Context `{! ApplicativeRespectsFunctor }.

  Local Instance fmap_respect'
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (fmap (A:=A) (B:=B)).
  Proof.
    unfold Proper ; logical_eqv_intro.
    repeat rewrite fapply_respect_fmap ; logical_eqv.
  Qed.

  Definition Deriving_FunctorWF_ApplicativeWF : FunctorWF t.
  Proof.
    constructor ; intros ; simpl.
    - rewrite fapply_respect_fmap ; logical_eqv ; simpl.
      rewrite fapply_unit ; logical_eqv.
    - rewrite fapply_respect_fmap ; logical_eqv.
      rewrite fapply_respect_fmap ; logical_eqv .
      rewrite fapply_respect_fmap ; logical_eqv ; simpl.
      rewrite fapply_composition ; logical_eqv ; simpl.
      rewrite fapply_homomorphism ; logical_eqv.
      rewrite fapply_homomorphism ; logical_eqv.
    - apply fmap_respect'.
  Qed.
End Deriving_FunctorWF_ApplicativeWF.