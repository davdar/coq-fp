Inductive nlist : nat -> Type :=
  | nnil : nlist O
  | ncons : forall n, unit -> nlist n -> nlist (S n).

Definition foo n (l:nlist n) : nat :=
  match l with
  | nnil => O
  | ncons m _ _ => n
  end.

Extraction foo.

  



Require Import FP.
Require Import FPNotation.

(*
Eval compute in intersperse ","%char (convert (to:=list ascii) "foo").
*)

Require Import Coq.Lists.List.

Class Functor t :=
  { fmap : forall {A B}, (A -> B) -> t A -> t B }.

Definition fmap2 {t u} {tF:Functor t} {uF:Functor u} {A B}
    (f:A -> B) : t (u A) -> t (u B) := fmap (fmap f).

Fixpoint list_map {A B} (f:A -> B) (xs:list A) : list B :=
  match xs with
  | nil => nil
  | x::xs' => f x::list_map f xs'
  end.

Instance list_Functor : Functor list :=
  { fmap := fun _ _ => list_map }.

Fixpoint prod_map {A B C} (f:A -> B) (p:(C*A)) : (C*B) :=
  let (c,a) := p in (c,f a).

Instance prod_Functor {A} : Functor (prod A) :=
  { fmap := fun _ _ => prod_map }.

Fixpoint len {A} (xs:list A) : nat :=
  match xs with
  | nil => O
  | _::xs' => S (len xs')
  end.

Definition foo_works1 : list (nat * list unit) -> list (nat * nat) :=
  fmap2 (t:=list) len.

(*
Definition foo_doesnt1 : list (nat * list unit) -> list (nat * nat) :=
  fmap2 len.
*)

Definition foo_works2 : list (nat * list unit) -> list (nat * nat).
  refine (_ len).
  apply fmap2.
  Defined.

(*
Definition foo_doesnt2 : list (nat * list unit) -> list (nat * nat).
  refine (_ len).
  exact fmap2.
  Defined.
*)

  
  