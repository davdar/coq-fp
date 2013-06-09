Require Import FP.CoreClasses.Setoid.
Require Import FP.CoreClasses.Eqv.

Class Bijection T U `{! Eqv T ,! Eqv U } :=
  { bij_to : T -> U
  ; bij_from : U -> T
  ; bij_from_to_eqv : forall x, eqv x x -> eqv (bij_from (bij_to x)) x
  ; bij_to_from_eqv : forall y, eqv y y -> eqv (bij_to (bij_from y)) y
  }.

Instance :
  forall T T' U U'
    `{! Eqv T ,! PER_WF T
     ,! Eqv T' ,! PER_WF T'
     ,! Eqv U ,! PER_WF U
     ,! Eqv U' ,! PER_WF U'
     ,! Bijection T T' ,! Bijection U U'
     },
  Bijection (T -> U) (T' -> U').
Proof.
  intros.
  refine(
    {| bij_to f x := bij_to (f (bij_from x))
     ; bij_from f x := bij_from (f (bij_to x))
     ; bij_from_to_eqv := _
     ; bij_to_from_eqv := _
    |})
  ; intros f fwf ; logical_eqv.
  - rewrite bij_from_to_eqv.
    + logical_eqv ; rewrite bij_from_to_eqv ; logical_eqv.
    + logical_eqv_elim_once ; auto.
      transitivity x ; [|symmetry] ; apply bij_from_to_eqv ; logical_eqv.
  - rewrite bij_to_from_eqv.
    + logical_eqv ; rewrite bij_to_from_eqv ; logical_eqv.
    + logical_eqv_elim_once ; auto.
      transitivity x ; [|symmetry] ; apply bij_to_from_eqv ; logical_eqv.
Qed.