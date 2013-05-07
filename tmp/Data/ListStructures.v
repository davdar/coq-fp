Require Import FP.Data.Ascii.
Require Import FP.Data.String.
Require Import FP.Data.List.
Require Import FP.Data.N.
Require Import FP.Data.NRelations.
Require Import FP.Data.NStructures.
Require Import FP.Data.Function.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Functor.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Show.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Functor.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.Iterable.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Functor.
Require Import FP.Structures.FZero.
Require Import FP.Structures.Traversable.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Comonad.
Require Import FP.Data.PrettyI.
Require Import FP.Structures.Monoid.

Import AdditiveNotation.
Import MonadNotation.
Import EqDecNotation.
Import ApplicativeNotation.
Import FunctionNotation.
Import CharNotation.
Import ListNotation.
Import MonoidNotation.
Import ComonadNotation.
Import StringNotation.
Import NNotation.

Section coercions.
  Context {m} {M:FUnit m} {MP:FZero m}.
  Definition coerce_cons {A} (xs:list A) : m (A*list A) :=
    match xs with
    | [] => fzero
    | x::xs => funit (x,xs)
    end.
End coercions.

Section Show.
  Context {A} {AS:Show A}.

  Section list_show.
    Variable (R:Type) (SR:ShowResult R).

    Fixpoint list_show_inner (xL:list A) : R :=
      match xL with
      | nil => gunit
      | x::xL' =>
             raw_string "; "
          ** show x
          ** list_show_inner xL'
      end.
          
    Definition list_show (xL:list A) : R :=
      match xL with
      | nil => raw_string "[]"
      | x::nil =>
             raw_char "["%char
          ** show x
          ** raw_char "]"%char
      | x1::x2::xL =>
             raw_char "["%char
          ** show x1
          ** list_show_inner (x2::xL)
          ** raw_char "]"%char
      end.
  End list_show.

  Global Instance list_Show : Show (list A) := { show := list_show }.
End Show.

Section Pretty.
  Context {A} {SP:Pretty A}.

  Fixpoint list_pretty_inner (xL:list A) :=
    match xL with
    | nil => nil_d
    | x::xL =>
        text_d "; " `concat_d`
        nest_d 2 (pretty x) `concat_d`
        line_d `concat_d`
        list_pretty_inner xL
    end.

  Fixpoint list_pretty (xL:list A) : doc :=
    match xL with
    | [] => text_d "[]"
    | [x] =>
      group_d begin
        text_d "[ " `concat_d`
        nest_d 2 (pretty x) `concat_d`
        line_d `concat_d`
        text_d "]"
      end
    | x1::x2::xL =>
      group_d begin
        text_d "[ " `concat_d`
        nest_d 2 (pretty x1) `concat_d`
        line_d `concat_d`
        list_pretty_inner (x2::xL) `concat_d`
        text_d "]"
      end
    end.
  Global Instance list_Pretty : Pretty (list A) := { pretty := list_pretty }.
    
End Pretty.

Section Monoid.
  Context {A:Type}.
  Global Instance list_Monoid : Monoid (list A) :=
    { monoid_times := app
    ; monoid_unit := nil
    }.
End Monoid.

Fixpoint list_cofold {A} {m} {M:Comonad m} {B}
    (f:A -> m B -> B) (bM:m B) (xs:list A) : B :=
  match xs with
  | [] => coret bM
  | x::xs =>
      let bM := codo bM => list_cofold f bM xs in
      f x bM
  end.
Instance list_Foldable {A} : Foldable A (list A) :=
  { cofold := @list_cofold _ }.

Fixpoint list_coiter {A} {m} {M:Comonad m} {B}
    (f:m B -> A -> B) (bM:m B) (xs:list A) : B :=
  match xs with
  | [] => coret bM
  | x::xs =>
      let bM := codo bM => f bM x in
      list_coiter f bM xs
  end.
Instance list_Iterable {A} : Iterable A (list A) :=
  { coiter := @list_coiter _ }.

Fixpoint list_sequence {u} {uA:Applicative u} {A}
    (xs:list (u A)) : u (list A) :=
  match xs with
  | nil => funit nil
  | x::xs' => funit cons <@> x <@> list_sequence xs'
  end.
Instance list_Traversable : Traversable list :=
  { tsequence := @list_sequence }.

Definition list_mbuild {A} {m} {M:Monad m}
  (fld:forall {B}, (A -> B -> B) -> B -> m B) : m (list A) :=
    fld cons nil.
Instance list_Buildable {A} : Buildable A (list A) :=
  { mbuild := @list_mbuild _ }.
    
Instance list_FMap : FMap list :=
  { fmap := @map }.

Fixpoint zip {A B} (xs:list A) (ys:list B) : list (A*B) :=
  match xs,ys with
  | nil,_ => nil
  | _,nil => nil
  | x::xs',y::ys' => (x,y)::zip xs' ys'
  end.

Fixpoint zip_with {A B C} (f:A -> B -> C) (xs:list A) (ys:list B) : list C :=
  match xs,ys with
  | nil, _ => nil
  | _, nil => nil
  | x::xs',y::ys' => f x y::zip_with f xs' ys'
  end.

Fixpoint unzip {A B} (xys:list (A*B)) : list A * list B :=
  match xys with
  | nil => (nil, nil)
  | (x,y)::xys' =>
      let (xs,ys) := unzip xys'
      in (x::xs,y::ys)
  end.

Fixpoint nth {A} (n:N) (xs:list A) : option A :=
  match xs with
  | [] => None
  | x::xs => if n =! 0 then Some x else nth (n - 1) xs
  end.

Section Monad.
  Definition list_funit {A} (a:A) : list A := [a].
  Global Instance list_FUnit : FUnit list :=
    { funit := @list_funit }.
                                    
  Fixpoint list_bind {A B} (xs:list A) (f:A -> list B) : list B :=
    match xs with
    | [] => []
    | x::xs => f x ** list_bind xs f
    end.
  Global Instance list_MBind : MBind list :=
    { bind := @list_bind }.
End Monad.

(*
Section MonadPlus.
  Definition list_mzero {A} : list A := [].
  Definition list_mplus {A B} (xs:list A) (ys:list B) : list (A+B) :=
    fmap inl xs ** fmap inr ys.
  Global Instance list_MonadPlus : MonadPlus list :=
    { mzero := @list_mzero
    ; mplus := @list_mplus
    }.
End MonadPlus.
*)

Section Groupish.
  Context {T} {T_GTimes : GTimes T} {T_GUnit : GUnit T}.

  Definition gproductr := foldr gtimes gunit.
  Definition gproductl := foldl gtimes gunit.
End Groupish.

(*
Section Alternative.
  Context {t} {F:FMap t} {A:Alternative t}.

  Definition fchoices {A} : list (t A) -> t A := foldr fchoice fzero.
End Alternative.
*)

Fixpoint replicateM {m A} {M:Monad m} (n:nat) (aM:m A) : m (list A) :=
  match n with
  | O => ret nil
  | S n' =>
      x <- aM ;;
      xs <- replicateM n' aM ;;
      ret $ cons x xs
  end.