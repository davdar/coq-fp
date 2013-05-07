Require Import FP.CoreClasses.PartialOrd.
Require Import FP.CoreClasses.Injection.
Require Import FP.CoreClasses.PreOrd.
Require Import FP.CoreClasses.Eqv.
Require Import FP.CoreData.Function.

Import PreOrdNotation.
Import FunctionNotation.
Import EqvNotation.

Class Lattice T :=
  { lmeet : T -> T -> T
  ; ljoin : T -> T -> T
  }.
Arguments lmeet {T Lattice} _ _ : simpl never.
Arguments ljoin {T Lattice} _ _ : simpl never.

Module LatticeNotation.
  Infix "/\" := lmeet.
  Infix "\/" := ljoin.
End LatticeNotation.
Import LatticeNotation.

Class LatticeWF T `{! Lte T ,! Eqv T ,! ER_WF T ,! PartialOrd T ,! Lattice T } :=
  { lmeet_ineq : forall t1 t2, ((t1 /\ t2) <= t1) `and` ((t1 /\ t2) <= t2)
  ; ljoin_ineq : forall t1 t2, (t1 <= (t1 \/ t2)) `and` (t2 <= (t1 \/ t2))
  }.

Class BoundedLattice T :=
  { ltop : T
  ; lbot : T
  }.
Arguments ltop {T BoundedLattice} : simpl never.
Arguments lbot {T BoundedLattice} : simpl never.

Class BoundedLatticeWF T `{! Lte T ,! Eqv T ,! ER_WF T ,! PartialOrd T ,! Lattice T ,! BoundedLattice T } :=
  { ltop_ineq : forall {t}, t <= ltop
  ; lbot_ineq : forall {t}, lbot <= t
  }.

Definition lmin {T} `{! Lattice T } : T -> T -> T := lmeet.
Definition lmax {T} `{! Lattice T } : T -> T -> T := ljoin.