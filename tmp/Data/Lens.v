Require Import FP.Data.Store.
Require Import FP.Data.Function.

Import FunctionNotation.

Inductive lens A S := Lens { un_lens : A -> store S A }.
Arguments Lens {A S} _.
Arguments un_lens {A S} _ _.

Section lens.
  Context {A B:Type}.

  Definition run_lens (l:lens A B) : A -> A := run_store '.' un_lens l.

  Definition mk_lens (get:A -> B) (set:B -> A -> A) : lens A B :=
    Lens $ fun a => Store (fun s => set s a) (get a).
  Definition iso_lens (from:B -> A) (to:A -> B) : lens A B :=
    Lens $ Store from '.' to.

  Definition lcompose {C} (lg:lens B C) (lf:lens A B) : lens A C :=
    Lens $ fun a =>
      let '(Store f s1) := un_lens lf a in
      let '(Store g s2) := un_lens lg s1 in
      Store (f '.' g) s2.
  Definition lfocus {C} : lens A B -> lens B C -> lens A C :=
    flip lcompose.

  Definition lget (l:lens A B) (a:A) : B :=
    store_pos $ un_lens l a.
  Definition laccess : A -> lens A B -> B :=
    flip lget.

  Definition lmodify {A S} (l:lens A S) (f:S -> S) : lens A S :=
    Lens $ store_update f '.' un_lens l.
  Definition lset {A S} (l:lens A S) (s:S) : lens A S :=
    lmodify l (const s).
End lens.

Module LensNotation.
  Infix "!" := lfocus (at level 61, right associativity).
  Infix "@" := laccess (at level 63, no associativity).
  Infix ":%" := lmodify (at level 62, no associativity).
  Infix ":<-" := lset (at level 62, no associativity).
End LensNotation.