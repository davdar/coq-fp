Require Export FP.Data.ListPre.

Require Import FP.Data.AsciiPre.
Require Import FP.Data.BoolPre.
Require Import FP.Data.FunctionPre.
Require Import FP.Data.StringPre.

Require Import FP.Data.N.
Require Import FP.Data.Option.
Require Import FP.Data.State.
Require Import FP.Data.Z.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Iterable.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Peano.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Show.
Require Import FP.Structures.Traversable.
Require Import FP.Data.PrettyI.

Import AdditiveNotation.
Import ApplicativeNotation.
Import BoolNotation.
Import CharNotation.
Import ComonadNotation.
Import EqDecNotation.
Import EqvNotation.
Import FunctionNotation.
Import FunctorNotation.
Import ListNotation.
Import MonadNotation.
Import MonoidNotation.
Import OrdNotation.
Import StringNotation.

Section coercions.
  Context {m} {M:Monad m} {MP:MonadPlus m}.
  Definition coerce_cons {A} (xs:list A) : m (A*list A) :=
    match xs with
    | [] => mzero
    | x::xs => ret (x,xs)
    end.
End coercions.

Section EqDec.
  Context {A} {AED:EqDec A}.

  Fixpoint list_eq_dec (xL:list A) (yL:list A) : bool :=
    match xL, yL with
    | nil, nil => true
    | x::xL', y::yL' => x '=! y && list_eq_dec xL' yL'
    | _, _ => false
    end.

  Global Instance list_EqDec : EqDec (list A) := { eq_dec := list_eq_dec }.

  Context {ARDC:RelDecCorrect (T:=A) eq_dec eq}.

  Global Instance list_Eq_RelDecCorrect : RelDecCorrect (T:=list A) eq_dec eq.
  Admitted.
End EqDec.

Section Eqv.
  Context {A} {AE:Eqv A}.

  Inductive list_eqv : list A -> list A -> Prop :=
    | NilEqv : list_eqv nil nil
    | ConsEqv : forall x y xL yL, x '~= y -> list_eqv xL yL -> list_eqv (x::xL) (y::yL).

  Global Instance list_Eqv : Eqv (list A) := { eqv := list_eqv }.

  Context {AEE:Equivalence (A:=A) eqv}.

  Global Instance list_Equivalence : Equivalence (A:=list A) eqv.
  Admitted.
End Eqv.

Section EqvDec.
  Context {A B} {AED:EqvDec A} {BED:EqvDec B}.

  Fixpoint list_eqv_dec (xL:list A) (yL:list A) : bool :=
    match xL, yL with
    | nil, nil => true
    | x::xL', y::yL' => x '~=! y && list_eqv_dec xL' yL'
    | _, _ => false
    end.

  Global Instance list_EqvDec : EqvDec (list A) := { eqv_dec := list_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect (T:=A) eqv_dec eqv}.

  Global Instance list_Eqv_RelDecCorrect : RelDecCorrect (T:=list A) eqv_dec eqv.
  Admitted.
End EqvDec.

Section Ord.
  Context {A} {AL:Ord A}.

  Inductive list_lt : list A -> list A -> Prop :=
    | NilLte : forall x xL,
        list_lt nil (x::xL)
    | HeadLte : forall x y xL yL,
        x '< y -> list_lt (x::xL) (y::yL)
    | TailLte : forall x y xL yL,
        x '~= y -> list_lt xL yL -> list_lt (x::xL) (y::yL).

  Global Instance list_Ord : Ord (list A) := { lt := list_lt }.
End Ord.

Section OrdDec.
  Context {A:Type}.

  Fixpoint list_ord_dec_b (a_ord_dec:A -> A -> comparison) (xL:list A) (yL:list A) : comparison :=
    match xL, yL with
    | nil, nil => Eq
    | nil, _::_ => Lt
    | _::_, nil => Gt
    | x::xL', y::yL' =>
        match x `a_ord_dec` y with
        | Lt => Lt
        | Gt => Gt
        | Eq => list_ord_dec_b a_ord_dec xL' yL'
        end
    end.

  Context {ALD:OrdDec A}.

  Definition list_ord_dec : list A -> list A -> comparison := list_ord_dec_b ord_dec.

  Global Instance list_OrdDec : OrdDec (list A) := { ord_dec := list_ord_dec }.
End OrdDec.

Section Show.
  Context {A} {AS:Show A}.

  Section list_show.
    Variable (R:Type) (SR:ShowResult R).

    Fixpoint list_show_inner (xL:list A) :=
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
  Global Instance list_Monoid : forall {A}, Monoid (list A) :=
    { Monoid_Semigroup := {| gtimes := app |}
    ; gunit := nil
    }.
End Monoid.

Fixpoint list_cofold {A} {m} {M:Comonad m} {B} (f:A -> m B -> B) (bM:m B) (xs:list A) : B :=
  match xs with
  | [] => coret bM
  | x::xs =>
      let bM := codo bM => list_cofold f bM xs in
      f x bM
  end.
Instance list_Foldable {A} : Foldable A (list A) :=
  { cofold := @list_cofold _ }.

Fixpoint list_coiter {A} {m} {M:Comonad m} {B} (f:m B -> A -> B) (bM:m B) (xs:list A) : B :=
  match xs with
  | [] => coret bM
  | x::xs =>
      let bM := codo bM => f bM x in
      list_coiter f bM xs
  end.
Instance list_Iterable {A} : Iterable A (list A) :=
  { coiter := @list_coiter _ }.

Fixpoint list_sequence {u} {uA:Applicative u} {A} (xs:list (u A)) : u (list A) :=
  match xs with
  | nil => fret nil
  | x::xs' => fret cons <@> x <@> list_sequence xs'
  end.
Instance list_Traversable : Traversable list :=
  { tsequence := @list_sequence }.

Definition list_mbuild {A} {m} {M:Monad m}
  (fld:forall {B}, (A -> B -> B) -> B -> m B) : m (list A) :=
    fld cons nil.
Instance list_Buildable {A} : Buildable A (list A) :=
  { mbuild := @list_mbuild _ }.
    
Section Functor.
  Global Instance list_Functor : Functor list :=
    { fmap := fun _ _ => map }.
End Functor.

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
  | x::xs => if n '=! 0 then Some x else nth (n `BinNat.N.sub` 1) xs
  end.

Section Monad.
  Definition list_ret {A} (a:A) : list A := [a].
  Fixpoint list_bind {A B} (xs:list A) (f:A -> list B) : list B :=
    match xs with
    | [] => []
    | x::xs => f x ** list_bind xs f
    end.
  Global Instance list_Monad : Monad list :=
    { ret := @list_ret
    ; bind := @list_bind
    }.
End Monad.

Section MonadPlus.
  Definition list_mzero {A} : list A := [].
  Definition list_mplus {A B} (xs:list A) (ys:list B) : list (A+B) :=
    fmap inl xs ** fmap inr ys.
  Global Instance list_MonadPlus : MonadPlus list :=
    { mzero := @list_mzero
    ; mplus := @list_mplus
    }.
End MonadPlus.

Section GeneralizedList.
  Definition map {T A U B} {TF:Foldable A T} {UB:Buildable B U}
      (f:A -> B) (t:T) : U :=
    build $ fun C (cons:B -> C -> C) (nil:C) =>
      fold (fun (a:A) (c:C) => cons (f a) c) nil t.

  Definition foreach {T A U B} {TF:Foldable A T} {UB:Buildable B U}
      : T -> (A -> B) -> U := flip map.

  Definition filter {T A U} {TF:Foldable A T} {UB:Buildable A U}
      (f:A -> bool) (t:T) : U :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      fold (fun (a:A) (c:C) => if f a then cons a c else c) nil t.

  Definition select {T A} {TF:Foldable A T} (p:A -> bool) : T -> option A :=
    lazyfold begin fun C (a:A) (k:C -> option A) (l:C) =>
      if p a then Some a else k l
    end None.

  Definition lookup {T A B} {E:EqvDec A} {TF:Foldable (A*B) T} (a:A)
      : T -> option B :=
    fmap snd <.> select (fun (p:A*B) => fst p '~=! a).
  
  Definition cat_options {T A U} {TF:Foldable (option A) T} {UB:Buildable A U}
      (t:T) : U :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      fold (fun (aM:option A) (c:C) => fold cons c aM) nil t.

  Definition numbered {T A U} {TF:Foldable A T} {UB:Buildable (N*A) U}
      (t:T) : U :=
    eval_state 0 $ mbuild $ fun C (cons:N*A -> C -> C) (nil:C) =>
      mfold begin fun (a:A) (c:C) =>
        n <- get ;;
        modify psucc ;;
        ret $ cons (n,a) c
      end nil t.

  Definition intersperse {T A U} {TF:Foldable A T} {UB:Buildable A U}
      (i:A) (t:T) : U :=
    eval_state false $ mbuild $ fun C (cons:A -> C -> C) (nil:C) =>
      mfold begin fun (a:A) (c:C) =>
        b <- get ;;
        put true ;;
        ret $ if b:bool then
          cons a (cons i c)
        else
          cons a c 
      end nil t.

  Definition replicate {T A} {TB:Buildable A T} (n:N) (a:A) : T :=
    build $ fun C (cons:A -> C -> C) (nil:C) =>
      loopr (cons a) nil n.

  Definition length {T A} {TF:Foldable A T} {P} {Peano:Peano P} (t:T) : P :=
    exec_state pzero $
      mfold begin fun (_:A) (_:unit) =>
        pinc ;; ret tt
      end tt t.
    
              
End GeneralizedList.

Section Groupish.
  Context {T} {T_GTimes : GTimes T} {T_GUnit : GUnit T}.

  Definition gproductr := foldr gtimes gunit.
  Definition gproductl := foldl gtimes gunit.
End Groupish.

Section Alternative.
  Context {t} {F:Functor t} {A:Alternative t}.

  Definition fchoices {A} : list (t A) -> t A := foldr fchoice fzero.
End Alternative.

Fixpoint replicateM {m A} {M:Monad m} (n:nat) (aM:m A) : m (list A) :=
  match n with
  | O => ret nil
  | S n' =>
      x <- aM ;;
      xs <- replicateM n' aM ;;
      ret $ cons x xs
  end.