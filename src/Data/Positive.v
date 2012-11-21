Require BinNums.
Require BinPos.

Require Import FP.Data.AsciiPre.
Require Import FP.Data.FunctionPre.

Require Import FP.Data.Nat.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Iterable.
Require Import FP.Structures.Convertible.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.Ord.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Show.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Peano.

Import AdditiveNotation.
Import EqDecNotation.
Import FunctionNotation.
Import MonoidNotation.
Import ComonadNotation.


Definition positive := BinNums.positive.
Definition xH := BinNums.xH.
Definition xO := BinNums.xO.
Definition xI := BinNums.xI.

Module PositiveNotation.
  Delimit Scope positive_scope with positive.
End PositiveNotation.
Local Open Scope positive_scope.

Instance positive_nat_Convertible : Convertible positive nat :=
  { convert := BinPos.Pos.to_nat }.

Section EqDec.
  Global Instance pos_EqDec : EqDec positive := { eq_dec := BinPos.Pos.eqb }.
End EqDec.

Section Eqv.
  Global Instance pos_Eqv : Eqv positive := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance pos_EqvDec : EqvDec positive := { eqv_dec := eq_dec }.
End EqvDec.

Section Ord.
  Global Instance pos_Ord : Ord positive := { lt := BinPos.Pos.lt }.
End Ord.

Section OrdDec.
  Definition pos_ord_dec (z1:positive) (z2:positive) : comparison :=
    if z1 '=! z2 then Eq
    else if BinPos.Pos.ltb z1 z2 then Lt
    else Gt.
  Global Instance pos_OrdDec : OrdDec positive := { ord_dec := pos_ord_dec }.
End OrdDec.

Section Lattice.
  Global Instance pos_Lattice : Lattice positive :=
    { meet := BinPos.Pos.min
    ; join := BinPos.Pos.max
    }.
End Lattice.

Section Show.
  Definition pos_show {R} {SR:ShowResult R} : positive -> R := show <.> convert (to:=nat).
  Global Instance pos_Show : Show positive := { show := @pos_show }.
End Show.

Section Semiadditive.
  Definition pos_additive_Semigroup : Semigroup positive :=
    {| gtimes := BinPos.Pos.add |}.
  Global Instance Semiadditive_N : Semiadditive positive :=
    { Semiadditive_Semigroup := pos_additive_Semigroup }.
End Semiadditive.

Section Multiplicative.
  Definition multiplicative_pos_Monoid : Monoid positive :=
    {| Monoid_Semigroup := {| gtimes := BinPos.Pos.mul |}
     ; gunit := BinNums.xH
    |}.
  Global Instance Multiplicative_N : Multiplicative positive :=
    { Multiplicative_Monoid := multiplicative_pos_Monoid }.
End Multiplicative.

Fixpoint pos_cofold' {m} {M:Comonad m} {A}
    (f:positive -> m A -> A) (aM:m A) (n:positive) : A :=
  let double_cofold :=
    pos_cofold' $ fun n aM =>
      let aM := codo aM => f (xI n) aM in
      f (xO n) aM
  in
  match n with
  | xH => coret aM
  | xO n =>
      let aM := codo aM => double_cofold aM n in
      f xH aM
  | xI n =>
      let aM := codo aM => f (xO n) aM in
      let aM := codo aM => double_cofold aM n in
      f xH aM
  end.
Definition pos_cofold {m} {M:Comonad m} {A}
    (f:positive -> m A -> A) (aM:m A) (n:positive) : A :=
  let aM := codo aM => f n aM in
  pos_cofold' f aM n.
Instance pos_Foldable : Foldable positive positive :=
  { cofold := @pos_cofold }.

Fixpoint pos_coiter' {m} {M:Comonad m} {A}
    (f:m A -> positive -> A) (aM:m A) (n:positive) : A :=
  let double_cofold :=
    pos_coiter' $ fun aM n =>
      let aM := codo aM => f aM (xO n) in
      f aM (xI n)
  in
  match n with
  | xH => coret aM
  | xO n =>
      let aM := codo aM => f aM xH in
      double_cofold aM n
  | xI n =>
      let aM := codo aM => f aM xH in
      let aM := codo aM => double_cofold aM n in
      f aM (xO n)
  end.
Definition pos_coiter {m} {M:Comonad m} {A}
    (f:m A -> positive -> A) (aM:m A) (n:positive) : A :=
  let aM := codo aM => pos_coiter' f aM n in
  f aM n.
Instance pos_Iterable : Iterable positive positive :=
  { coiter := @pos_coiter }.

Fixpoint pos_coloopr' {m} {M:Comonad m} {A}
    (f:m A -> A) (aM:m A) (n:positive) : A :=
  let double_coloopr :=
    pos_coloopr' $ fun aM =>
      let aM := codo aM => f aM in
      f aM
  in
  match n with
  | xH => coret aM
  | xO n =>
      let aM := codo aM => double_coloopr aM n in
      f aM
  | xI n =>
      let aM := codo aM => double_coloopr aM n in
      let aM := codo aM => f aM in
      f aM
  end.
Definition pos_coloopr {m} {M:Comonad m} {A}
    (f:m A -> A) (aM:m A) (n:positive) : A :=
  let aM := codo aM => pos_coloopr' f aM n in
  f aM.

Fixpoint pos_coloopl' {m} {M:Comonad m} {A}
    (f:m A -> A) (aM:m A) (n:positive) : A :=
  let double_coloopl :=
    pos_coloopl' $ fun aM =>
      let aM := codo aM => f aM in
      f aM
  in
  match n with
  | xH => coret aM
  | xO n =>
      let aM := codo aM => f aM in
      double_coloopl aM n
  | xI n =>
      let aM := codo aM => f aM in
      let aM := codo aM => f aM in
      double_coloopl aM n
  end.
Definition pos_coloopl {m} {M:Comonad m} {A}
    (f:m A -> A) (aM:m A) (n:positive) : A :=
  let aM := codo aM => f aM in
  pos_coloopl' f aM n.
Instance pos_Peano : Peano positive :=
  { pzero := xH
  ; psucc := BinPos.Pos.succ
  ; coloopr := @pos_coloopr
  ; coloopl := @pos_coloopl
  }.

(*
Require Import FP.Structures.Functor.
Require Import FP.Data.Option.

Definition fix_fact (fuel:positive) : positive -> option positive :=
  flip loopr_fix fuel $ fun fact n => 
    if n '=! 1 then
      Some n
    else
      fmap (times n) $ fact (BinPos.Pos.sub n 1).

Eval compute in fix_fact 1000000000 4.
*)