Require Import FP.CoreClasses.
Require Import FP.CoreData.

Import ProperNotation.
Import EqvNotation.

Class Category (t:Type -> Type -> Type) :=
  { cid : forall {A}, t A A
  ; ccompose : forall {A B C}, t B C -> t A B -> t A C
  }.
Arguments cid {t Category A} : simpl never.
Arguments ccompose {t Category A B C} _ _ : simpl never.

Section CategoryWF.
  Context t `{! Category t ,! Bif_Eqv t ,! Bif_PER_WF t }.

  Class CategoryWF :=
    { category_left_unit :
        forall
          {A} `{! Eqv A ,! PER_WF A}
          {B} `{! Eqv B ,! PER_WF B}
          (f:t A B) `{! Proper eqv f },
        ccompose cid f ~= f
    ; category_right_unit :
        forall
          {A} `{! Eqv A ,! PER_WF A}
          {B} `{! Eqv B ,! PER_WF B}
          (f:t A B) `{! Proper eqv f },
        ccompose f cid ~= f
    ; category_associativity :
        forall
          {A} `{! Eqv A ,! PER_WF A}
          {B} `{! Eqv B ,! PER_WF B}
          {C} `{! Eqv C ,! PER_WF C}
          {D} `{! Eqv D ,! PER_WF D}
          (f:t A B) `{! Proper eqv f }
          (g:t B C) `{! Proper eqv g }
          (h:t C D) `{! Proper eqv h },
        ccompose (ccompose h g) f ~= ccompose h (ccompose g f)
    }.
End CategoryWF.
Arguments CategoryWF t {_ _}.

Module CategoryNotation.
  Infix "<.>" := ccompose (at level 45, right associativity).
End CategoryNotation.