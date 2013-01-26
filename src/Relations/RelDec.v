Require Import FP.Data.BoolPre.
Require Import FP.Data.Function.
Require Import FP.Structures.Injection.

Import FunctionNotation.

Section RelDec.
  Context (T:Type).
  
  Class RelDecCorrect (R: T -> T -> Prop) (D:T -> T -> bool) : Prop :=
    { rel_correct : forall {x y}, R x y -> D x y = true
    ; dec_correct : forall {x y}, D x y = true -> R x y
    }.
End RelDec.
Arguments rel_correct {T R D RelDecCorrect x y _}.
Arguments dec_correct {T R D RelDecCorrect x y _}.

Section neg_rel_dec_correct.
  Context {T R D} {RDC:RelDecCorrect T R D}.

  Definition neg_rel_correct : forall {x y}, ~R x y -> D x y = false.
    intros.
    destruct (consider_bool (D x y)) ; auto.
    apply dec_correct in e.
    specialize (H e).
    contradiction.
    Qed.
  Definition neg_dec_correct : forall {x y}, D x y = false -> ~R x y.
    unfold "~" ; intros.
    apply rel_correct in H0.
    congruence.
    Qed.
End neg_rel_dec_correct.

Section rel_dec_p.
  Context {T R D} {RDWC:RelDecCorrect T R D}.

  Definition rel_dec_p (x:T) (y:T) : {R x y} + {~R x y}.
    destruct (consider_bool (D x y)) as [H | H].
    apply dec_correct in H ; eauto.
    apply neg_dec_correct in H ; eauto.
  Qed.

  Definition neg_rel_dec_p (x:T) (y:T) : {~R x y} + {R x y}.
  Proof. destruct (rel_dec_p x y) ; [ right | left ] ; auto. Qed.
End rel_dec_p.

