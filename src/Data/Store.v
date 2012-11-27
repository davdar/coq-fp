Require Import FP.Data.Function.

Import FunctionNotation.

Inductive store S A := Store
  { store_context : S -> A
  ; store_pos : S
  }.
Arguments Store {S A} _ _.
Arguments store_context {S A} _ _.
Arguments store_pos {S A} _.

(* Seek to a relative location *)
Definition seeks {S A} (f:S -> S) (st:store S A) : store S A :=
  let '(Store g s) := st in Store g (f s).

(* Seek to an absolute location *)
Definition seek {S A} (s:S) : store S A -> store S A := seeks $ const s.

(* Peek at a relative location *)
Definition peeks {S A} (f:S -> S) (st:store S A) : A :=
  let '(Store g s) := st in g $ f s.

(* Peek at an absolute location *)
Definition peek {S A} (s:S) : store S A -> A := peeks $ const s.