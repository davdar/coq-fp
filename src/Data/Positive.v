Require BinNums.
Require BinPos.

Require Import Data.AsciiPre.
Require Import Data.FunctionPre.

Require Import Data.Nat.
Require Import Relations.RelDec.
Require Import Structures.Additive.
Require Import Structures.Convertible.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Lattice.
Require Import Structures.Monoid.
Require Import Structures.Multiplicative.
Require Import Structures.Ord.
Require Import Structures.RelationClasses.
Require Import Structures.Show.
Require Import Structures.Comonad.
Require Import Structures.Foldable.
Require Import Structures.Peano.

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
Import PositiveNotation.

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

Fixpoint pos_cofoldr' {m} {M:Comonad m} {A}
    (f:positive -> m A -> A) (aM:m A) (n:positive) : A :=
  let double_cofold :=
    pos_cofoldr' $ fun n aM =>
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
Definition pos_cofoldr {m} {M:Comonad m} {A}
    (f:positive -> m A -> A) (aM:m A) (n:positive) : A :=
  let aM := codo aM => f n aM in
  pos_cofoldr' f aM n.
Instance pos_FoldableR : FoldableR positive positive :=
  { cofoldr := @pos_cofoldr }.

Fixpoint pos_cofoldl' {m} {M:Comonad m} {A}
    (f:m A -> positive -> A) (aM:m A) (n:positive) : A :=
  let double_cofold :=
    pos_cofoldl' $ fun aM n =>
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
Definition pos_cofoldl {m} {M:Comonad m} {A}
    (f:m A -> positive -> A) (aM:m A) (n:positive) : A :=
  let aM := codo aM => pos_cofoldl' f aM n in
  f aM n.
Instance pos_FoldableL : FoldableL positive positive :=
  { cofoldl := @pos_cofoldl }.

Fixpoint pos_coiterr' {m} {M:Comonad m} {A}
    (f:m A -> A) (aM:m A) (n:positive) : A :=
  let double_coiter :=
    pos_coiterr' $ fun aM =>
      let aM := codo aM => f aM in
      f aM
  in
  match n with
  | xH => coret aM
  | xO n =>
      let aM := codo aM => double_coiter aM n in
      f aM
  | xI n =>
      let aM := codo aM => double_coiter aM n in
      let aM := codo aM => f aM in
      f aM
  end.
Definition pos_coiterr {m} {M:Comonad m} {A}
    (f:m A -> A) (aM:m A) (n:positive) : A :=
  let aM := codo aM => pos_coiterr' f aM n in
  f aM.
Instance pos_PeanoR : PeanoR positive :=
  { coiterr := @pos_coiterr }.

Fixpoint pos_coiterl' {m} {M:Comonad m} {A}
    (f:m A -> A) (aM:m A) (n:positive) : A :=
  let double_coiter :=
    pos_coiterl' $ fun aM =>
      let aM := codo aM => f aM in
      f aM
  in
  match n with
  | xH => coret aM
  | xO n =>
      let aM := codo aM => f aM in
      double_coiter aM n
  | xI n =>
      let aM := codo aM => f aM in
      let aM := codo aM => f aM in
      double_coiter aM n
  end.
Definition pos_coiterl {m} {M:Comonad m} {A}
    (f:m A -> A) (aM:m A) (n:positive) : A :=
  let aM := codo aM => f aM in
  pos_coiterl' f aM n.
Instance pos_PeanoL : PeanoL positive :=
  { coiterl := @pos_coiterl }.

(*
Require Import Structures.Functor.
Require Import Data.Option.

Definition ffix_fact (fuel:positive) : positive -> option positive :=
  flip ffix fuel $ fun fact n => 
    if n '=! 1%positive then
      Some n
    else
      fmap (times n) $ fact (BinPos.Pos.sub n 1%positive).

Eval compute in ffix_fact 1000000000%positive 4%positive.
*)