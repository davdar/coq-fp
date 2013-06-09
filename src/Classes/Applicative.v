Require Import FP.CoreData.
Require Import FP.CoreClasses.

Import FunctionNotation.
Import ProperNotation.
Import EqvNotation.

Class Applicative t :=
  { fret : forall {A}, A -> t A
  ; fapply : forall {A B}, t (A -> B) -> t A -> t B
  }.
Arguments fret {t Applicative A} _ : simpl never.
Arguments fapply {t Applicative A B} _ _ : simpl never.

Section Applicative.
  Context {t} `{! Applicative t }.

  Definition fapply_fmap {A B} : (A -> B) -> t A -> t B :=
    fapply '.' fret.
  Definition fapply_ftimes {A B} (aT:t A) (bT:t B) : t (A*B) :=
    fapply (fapply (fret pair) aT) bT.
End Applicative.
Arguments fapply_fmap {t _ A B} _ _ / . 
Arguments fapply_ftimes {t _ A B} _ _ / .

Module ApplicativeNotation.
  Infix "<@>" := fapply (at level 47, left associativity).
End ApplicativeNotation.

Section ApplicativeWF.
  Context {t} `{! Applicative t ,! F_Eqv t ,! F_PER_WF t }.

  Class ApplicativeWF :=
    { Applicative_unit :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (aT:t A) `{! Proper eqv aT },
        fapply (fret id) aT ~= aT
    ; Applicative_composition :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          {C} `{! Eqv C ,! PER_WF C }
          (fT:t (A -> B)) `{! Proper eqv fT}
          (gT:t (B -> C)) `{! Proper eqv gT}
          (aT:t A) `{! Proper eqv aT },
        fapply gT (fapply fT aT)
        ~= fapply (fapply (fapply (fret compose) gT) fT) aT
    ; Applicative_homomorphism :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (f:A -> B) `{! Proper eqv f }
          (a:A) `{! Proper eqv a },
        fapply (fret f) (fret a) ~= fret (f a)
    (* is this derivable? necessary? *)
    ; Applicative_interchange :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (fT:t (A -> B)) `{! Proper eqv fT }
          (a:A) `{! Proper eqv a },
        fapply fT (fret a) ~= fapply (fret (apply_to a)) fT
    ; fret_Proper :>
        forall {A} `{! Eqv A ,! PER_WF A },
        Proper eqv (fret (A:=A))
    ; fapply_Proper :>
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B },
        Proper eqv (fapply (A:=A) (B:=B))
    }.
End ApplicativeWF.
Arguments ApplicativeWF t {_ _}. 
Hint Extern 9 (Proper eqv (fret (t:=?t) (A:=?A))) =>
  let H := fresh "H" in
  pose (H:=(fret_Proper (t:=t) (A:=A))) ; apply H
  : typeclass_instances.
Hint Extern 9 (Proper eqv (fapply (t:=?t) (A:=?A) (B:=?B))) =>
  let H := fresh "H" in
  pose (H:=(fapply_Proper (t:=t) (A:=A) (B:=B))) ; apply H
  : typeclass_instances.
