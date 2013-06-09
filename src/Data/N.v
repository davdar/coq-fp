Require Coq.NArith.BinNat.

Require Import FP.CoreData.
Require Import FP.Classes.
Require Import FP.Data.Positive.

Import ClassesNotation.

Instance N_Zero : Zero N := { zero := BinNat.N.zero }.
Instance N_Plus : Plus N := { plus := BinNat.N.add }.

Definition N_cofold {w} `{! Comonad w } {A} (f:N -> w A -> A) (aW:w A) (n:N) : A :=
  let aW := codo aW =>
    match n with
    | N0 => coret aW
    | Npos p => cofold (fun p aW => f (Npos p) aW) aW p
    end
  in
  f N0 aW.
Instance N_Foldable : Foldable N N := { cofold := @N_cofold }.

Definition N_coiter {w} `{! Comonad w } {A} (f:w A -> N -> A) (aW:w A) (n:N) : A :=
  let aW := codo aW => f aW N0 in
  match n with
  | N0 => coret aW
  | Npos p => coiter (fun aW p => f aW (Npos p)) aW p
  end.
Instance N_Iterable : Iterable N N := { coiter := @N_coiter }.

Definition N_coloopr {w} `{! Comonad w } {A} (f:w A -> A) (aW:w A) (n:N) : A :=
  match n with
  | N0 => coret aW
  | Npos p => coloopr f aW p
  end.
Definition N_coloopl {w} `{! Comonad w } {A} (f:w A -> A) (aW:w A) (n:N) : A :=
  match n with
  | N0 => coret aW
  | Npos p => coloopl f aW p
  end.
Instance N_Peano : Peano N :=
  { pzero := N0
  ; psucc := BinNat.N.succ
  ; coloopr := @N_coloopr
  ; coloopl := @N_coloopl
  }.