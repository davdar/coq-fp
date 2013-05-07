Require Import FP.Data.Function.

Import FunctionNotation.

Inductive store S A := Store
  { store_context : S -> A
  ; store_pos : S
  }.
Arguments Store {S A} _ _.
Arguments store_context {S A} _ _.
Arguments store_pos {S A} _.

Section store.
  Context {S A:Type}.
  Definition run_store (st:store S A) : A :=
    let '(Store g s) := st in g s.

  (* Update the focused state *)
  Definition store_update (f:S -> S) (st:store S A) : store S A :=
    let '(Store g s) := st in Store g (f s).

  (* Set the focuses state *)
  Definition store_set : S -> store S A -> store S A := store_update '.' const.
End store.
