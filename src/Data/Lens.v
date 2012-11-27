Require Import FP.Data.Store.
Require Import FP.Data.Function.

Import FunctionNotation.

Inductive lens A S := Lens { un_lens : A -> store S A }.
Arguments Lens {A S} _.
Arguments un_lens {A S} _ _.

Definition mk_lens {A S} (get:A -> S) (set:S -> A -> A) : lens A S :=
  Lens $ fun a => Store (fun s => set s a) (get a).
Definition iso_lens {A B} (from:B -> A) (to:A -> B) : lens A B :=
  Lens $ Store from <.> to.

Definition lcompose {A S1 S2} (lg:lens S1 S2) (lf:lens A S1) : lens A S2 :=
  Lens $ fun a =>
    let '(Store f s1) := un_lens lf a in
    let '(Store g s2) := un_lens lg s1 in
    Store (f <.> g) s2.
Definition lfocus {A S1 S2} : lens A S1 -> lens S1 S2 -> lens A S2 :=
  flip lcompose.
                        
Definition lget {A S} (l:lens A S) (a:A) : S :=
  store_pos $ un_lens l a.
Definition laccess {A S} : A -> lens A S -> S :=
  flip lget.

Definition lmodify {A S} (l:lens A S) (f:S -> S) : A -> A :=
  peeks f <.> un_lens l.

Definition lset {A S} (l:lens A S) (s:S) : A -> A :=
  lmodify l (const s).

Definition lupdate {A} : A -> (A -> A) -> A := apply_to.

Module LensNotation.
  Infix "'.'" := lfocus (at level 61, right associativity).
  Infix "'|'" := laccess (at level 63, no associativity).
  Infix "':%'" := lmodify (at level 62, no associativity).
  Infix "':='" := lset (at level 62, no associativity).
  Infix "':|'" := lupdate (at level 63, no associativity).
End LensNotation.