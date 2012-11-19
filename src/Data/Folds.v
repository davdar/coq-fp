(*

A demonstration of different folding strategies on positive

Note that actual foldr and foldr variants have been discovered, they are in Positive.v

Although, the point of this file is to compare comonad folding, monadic folding, and derived variants

Require Import Data.Positive.
Require Import Data.Function.
Require Import Structures.Monad.
Require Import Data.Identity.
Require Import Data.Cont.
Require Import Structures.Additive.
Require Import Structures.Multiplicative.
Require Import Structures.MonadCont.
Require Import Structures.EqDec.
Require Import Structures.Functor.
Require Import Data.Option.
Require Import Data.Susp.
Require Import Structures.Comonad.

Import SuspNotation.
Import PositiveNotation.
Import MonadNotation.
Import FunctionNotation.
Import AdditiveNotation.
Import MultiplicativeNotation.
Import EqDecNotation.
Import FunctorNotation.
Import ComonadNotation.

Definition small : positive :=  1000%positive.
Definition medium : positive := 10000%positive.
Definition large : positive :=  100000%positive.
Definition larger : positive := 1000000%positive.

Section RegularFolding.
  Definition iter {A}
      (fold:forall {A}, (A -> positive -> A) -> A -> positive -> A)
      (f:A -> A) : A -> positive -> A :=
    fold (fun a _ => f a).

  Definition do_sum
      (fold:forall A, (A -> positive -> A) -> A -> positive -> A)
      (n:positive) : positive :=
    iter fold (fun (p:positive) => p + 1%positive) 1%positive n.

  Definition mfix {A B}
      (fold:forall A, (A -> positive -> A) -> A -> positive -> A)
      (ff:(A -> option B) -> A -> option B) : positive -> A -> option B :=
    iter fold ff (fun _ => None).

  Definition lazy_k_fix {A B}
      (fold:forall A, (A -> positive -> A) -> A -> positive -> A)
      (ff:(A -> option B) -> A -> option B) : positive -> A -> option B :=
    run_cont <.> 
      iter fold
           (fun (aM:cont (A -> option B) (A -> option B)) =>
              callcc $
                 fun (k:(A -> option B) -> cont (A -> option B) (A -> option B)) =>
                   k $ fun (a:A) => ff (fun (a:A) => run_cont aM a) a)
         (ret $ const None).

  Definition fact
      (fold:forall A, (A -> positive -> A) -> A -> positive -> A)
      : positive -> positive -> option positive :=
    mfix fold $ fun fact n =>
      if n '=! 1%positive then
        Some n
      else
        fmap (times n) $ fact (BinPos.Pos.sub n 1%positive).

  Definition lazy_k_fact
      (fold:forall A, (A -> positive -> A) -> A -> positive -> A)
      : positive -> positive -> option positive :=
    lazy_k_fix fold $ fun fact n =>
      if n '=! 1%positive then
        Some n
      else
        fmap (times n) $ fact (BinPos.Pos.sub n 1%positive).
  
End RegularFolding.

Section MendlerFolding.
  Definition iter_z {A}
      (fold:forall {A}, (forall {B}, positive -> (B -> A) -> B -> A) -> A -> positive -> A)
      (f:forall {B}, (B -> A) -> B -> A) : A -> positive -> A :=
    fold (fun _ _ k b => f k b).

  Definition do_sum_z
      (fold:forall A, (forall {B}, positive -> (B -> A) -> B -> A) -> A -> positive -> A)
      (n:positive) : positive :=
    iter_z fold (fun _ k b => k b + 1%positive) 1%positive n.

  Definition mfix_z {A B}
      (fold:forall A, (forall {B}, positive -> (B -> A) -> B -> A) -> A -> positive -> A)
      (ff:(A -> option B) -> A -> option B) : positive -> A -> option B :=
    iter_z fold (fun _ k b => ff (fun (a:A) => k b a)) (fun _ => None).

  Definition fact_z
      (fold:forall A, (forall {B}, positive -> (B -> A) -> B -> A) -> A -> positive -> A)
      : positive -> positive -> option positive :=
    mfix_z fold $ fun fact n =>
      if n '=! 1%positive then
        Some n
      else
        fmap (times n) $ fact (BinPos.Pos.sub n 1%positive).
End MendlerFolding.

(* ----- standard fold ----- *)

Fixpoint pos_fold' {A} (f:A -> positive -> A) (a:A) (n:positive) : A :=
  let twice :=
    pos_fold' (fun a n => (a `f` xO n) `f` xI n)
              (a `f` xH)
  in
  match n with
  | xH => a
  | xO n => twice n
  | xI n => twice n `f` xO n
  end.
Definition pos_fold {A} (f:A -> positive -> A) (a:A) (n:positive) : A :=
  pos_fold' f a n `f` n.

Eval compute in pos_fold (flip cons) nil 10%positive.
Eval compute in do_sum (@pos_fold) medium.
(*
Eval compute in do_sum (@pos_fold) large.
*)
(* stalls
Eval compute in fact (@pos_fold) large 2%positive.
*)
Eval compute in lazy_k_fact (@pos_fold) large 2%positive.

(* --- attempted lazy fold by instantiating A to (delay A) --- *)
Definition pos_fold_lazy {A}
    (f:forall {B}, positive -> (B -> A) -> B -> A) (a:A) : positive -> A :=
  force <.> pos_fold (fun (aM:susp A) n =>
                        ret $
                          f n force aM)
                     (ret a).

Eval compute in pos_fold_lazy (fun _ n k b => flip cons (k b) n) nil 10%positive.
Eval compute in do_sum_z (@pos_fold_lazy) medium.
(*
Eval compute in do_sum_z (@pos_fold_lazy) large.
*)
(* stalls
Eval compute in fact_z (@pos_fold_lazy) large 2%positive.
*)

(* --- monadic fold by instantiating A to (m A) --- *)

Definition pos_fold_derived_m {m} {M:Monad m} {A}
    (f:A -> positive -> m A) (a:A) : positive -> m A :=
  pos_fold (fun (aM:m A) n => a <- aM ;; f a n) (ret a).

(* --- comonadic fold by instantiating A to (m A) -- *)

Definition pos_fold_derived_cm {m} {M:Comonad m} {A}
    (f:m A -> positive -> A) : m A -> positive -> A :=
  coret <..> pos_fold (fun (aM:m A) n => codo aM => f aM n).

(* --- reversed fold by instantiating monad m to cont --- *)

Definition pos_fold_derived_r {A} (f:A -> positive -> A) : A -> positive -> A :=
  run_cont <..> pos_fold_derived_m (fun (a:A) n =>
                                      callcc $ fun (k:A -> cont A A) =>
                                        a <- k a ;;
                                        ret $ a `f` n).

Eval compute in pos_fold_derived_r (flip cons) nil 10%positive.
Eval compute in do_sum (@pos_fold_derived_r) medium.
(* stack-overflows
Eval compute in do_sum (@pos_fold_derived_r) large.
*)
(* stack-overflows
Eval compute in fact (@pos_fold_derived_r) large 2%positive.
*)

(* --- attempted lazy fold by instantiating comonad m to delay *)

Definition pos_fold_derived_cm_lazy {A}
    (f:forall {B}, positive -> (B -> A) -> B -> A) (a:A) : positive -> A :=
  pos_fold_derived_cm (fun (aM:susp A) n =>
                                   f n coret aM)
                                (delay | a).

Eval compute in pos_fold_derived_cm_lazy (fun _ n k b => flip cons (k b) n) nil 10%positive.
Eval compute in do_sum_z (@pos_fold_derived_cm_lazy) medium.
(* stack-overflows
Eval compute in do_sum_z (@pos_fold_derived_cm_lazy) large.
*)
(* stack-overflows
Eval compute in fact_z (@pos_fold_derived_cm_lazy) large 2%positive.
*)

(* ----- comonadic generic fold ----- *)

Fixpoint pos_fold_cm' {m} {M:Comonad m} {A}
    (f:m A -> positive -> A) (aM:m A) (n:positive) : m A :=
  let twice :=
    pos_fold_cm' (fun aM n => let a := codo aM => aM `f` xI n in
                              a `f` xO n)
                 (codo aM => aM `f` xH)
  in
  match n with
  | xH => aM
  | xO n => twice n
  | xI n =>
      codo aM -< twice n => aM `f` xO n
  end.
Definition pos_fold_cm {m} {M:Comonad m} {A}
    (f:m A -> positive -> A) (aM:m A) (n:positive) : m A :=
  codo aM -< pos_fold_cm' f aM n => aM `f` n.

(* --- standard fold by instantiating comonad to identity --- *)

Definition pos_fold_cm_identity {A} (f:A -> positive -> A) (a:A) (n:positive) : A :=
  run_identity $ pos_fold_cm (fun aM p => f (run_identity aM) p) (Identity a) n.

Eval compute in pos_fold_cm_identity (flip cons) nil 10%positive.
Eval compute in do_sum (@pos_fold_cm_identity) medium.
(*
Eval compute in do_sum (@pos_fold_cm_identity) large.
*)
(* stalls
Eval compute in fact (@pos_fold_cm_identity) large 2%positive.
*)

(* --- lazy fold by instantiating comonad m to delay --- *)

Definition pos_fold_cm_lazy {A}
    (f:forall {B}, positive -> (B -> A) -> B -> A) (a:A) : positive -> A :=
  coret <.> pos_fold_cm (fun (aM:susp A) (p:positive) =>
                           f p force aM)
                        (delay | a).

Eval compute in pos_fold_cm_lazy (fun _ n k b => flip cons (k b) n) nil 10%positive.
Eval compute in do_sum_z (@pos_fold_cm_lazy) medium.
(* stack-overflows
Eval compute in do_sum_z (@pos_fold_cm_lazy) large.
*)
(* fast! *)
Eval compute in fact_z (@pos_fold_cm_lazy) large 2%positive.

(* --- hand-coded mendler-style fold --- *)

Definition force {A} (f:unit -> A) : A := f tt.
Fixpoint pos_foldl_k' {A B}
    (f:forall {B}, positive -> (B -> A) -> B -> A)
    (k:B -> A) (b:B) (n:positive) : A :=
  let twice := 
    pos_foldl_k' (fun B n' (k:B -> A) (b:B) =>
                   f (xI n') force $ fun _ => (* id $ *)
                     f (xO n') force $ fun _ => (* id $ *)
                       k b)
                (fun b => f xH force $ fun _ => (* id $ *)
                   k b)
                b
  in
  match n with
  | xH => k b 
  | xO n' => twice n'
  | xI n' => f (xO n) force $ fun _ => (* id $ *)
               twice n'
  end.
Definition pos_foldl_k {A} (f:forall {B}, positive -> (B -> A) -> B -> A) (a:A) (n:positive) : A :=
  f n force $ fun _ => pos_foldl_k' (@f) id a n.

Eval compute in pos_foldl_k (fun _ n k b => flip cons (k b) n) nil 10%positive.
Eval compute in do_sum_z (@pos_foldl_k) medium.
(* stack overflows
Eval compute in do_sum_z (@pos_foldl_k) large.
*)
(* fast! *)
Eval compute in fact_z (@pos_foldl_k) large 2%positive.

Fixpoint pos_iter' {B} (f:B -> positive -> B) (b:B) (n:positive) : B :=
  match n with
  | xH => flip f xH b
  | xO n => pos_iter' (fun b n =>
                         flip f (xO n) $ flip f (xI n) b)
                      b 
                      n
  | xI n => pos_iter' (fun b n =>
                         flip f (xO n) $ flip f (xI n) b)
                      b
                      n
  end.
Definition pos_iter {B} (f:B -> positive -> B) (b:B) (n:positive) : B :=
  pos_iter' f b n.
Eval compute in pos_iter (flip cons) nil 4%positive.
             

(*
Fixpoint pos_fold_m' {m} {M:Monad m} {A} (f:A -> positive -> m A) (aM:m A) (n:positive) : m A :=
  let twice :=
    pos_fold_m' (fun a n =>
                         a <- f a (xO n) ;;
                         f a (xI n))
                  (a <- aM ;; f a xH)
  in
  match n with
  | xH => aM
  | xO n => twice n
  | xI n =>
      a <- twice n ;;
      f a (xO n)
  end.
Definition pos_fold_m {m} {M:Monad m} {A} (f:A -> positive -> m A) (a:A) (n:positive) : m A :=
  a <- pos_fold_m' f (ret a) n ;; f a n.

(* --- standard fold by instantiating monad to identity --- *)

Definition pos_fold_m_identity {A} (f:A -> positive -> A) (a:A) (n:positive) : A :=
  run_identity $ pos_fold_m (fun a p => ret $ f a p) a n.

Eval compute in pos_fold_m_identity (flip cons) nil 10%positive.
Eval compute in do_sum (@pos_fold_m_identity) medium.
(*
Eval compute in do_sum (@pos_fold_m_identity) large.
*)
(* stalls
Eval compute in fact (@pos_fold_m_identity) large 2%positive.
*)

(* ----- ----- *)

Definition pos_iterl_k {A} (f:forall {B}, (B -> A) -> B -> A) : A -> positive -> A :=
  pos_foldl_k $ fun _ => const f.
Fixpoint pos_foldl' {A} (f:positive -> A -> A) (a:A) (n:positive) : A :=
  let twice :=
    pos_foldl' (fun n' a =>
                  f (xI n') $
                    f (xO n') a)
               (f xH a)
  in
  match n with
  | xH => a
  | xO n' => twice n'
  | xI n' => f (xO n')
               (twice n')
  end.
Definition pos_foldl {A} (f:positive -> A -> A) (a:A) (n:positive) : A :=
  f n $ pos_foldl' f a n.
Definition pos_iterl {A} (f:A -> A) : A -> positive -> A := pos_foldl $ const f.

(* this can short circuit, but stack-overflows if you use the whole thing *)

(* from timing, is a little faster than foldl *)
Fixpoint pos_foldr'' {A}
    (f:positive -> A -> (A -> A) -> A)
    (a:A) (n:positive) (k:A -> A) : A :=
  let twice a' n' :=
    pos_foldr'' (fun n' a' k =>
                   f (xI n') a' $ fun a' =>
                     f (xO n') a' k)
                a'
                n'
                (fun a' =>
                   f xH a' k)
  in
  match n with
  | xH => k a
  | xO n' => twice a n'
  | xI n' => f (xO n') a $ fun a =>
               twice a n'
  end.

Definition pos_foldr' {A}
    (f:positive -> A -> (A -> A) -> A)
    (a:A) (n:positive) (k:A -> A) : A :=
  f n a $ fun a => pos_foldr'' f a n k.
Definition pos_foldr {A} (f:positive -> A -> A) (a:A) (n:positive) : A :=
  pos_foldr' (fun n' a' k => k $ f n' a') a n id.
Definition pos_foldr2 {A} (f:positive -> A -> A) (a:A) (n:positive) : A :=
  pos_foldr' (fun n' a' k => f n' (k a')) a n id.
Definition pos_iterr {A} (f:A -> A) : A -> positive -> A :=
  pos_foldr $ const f.

Definition force_eta {A B} (f:unit -> A -> B) (a:A) : B := f tt a.
Fixpoint pos_foldr_k'' {A C}
    (f:forall {C}, positive -> A -> (C -> A -> A) -> C -> A)
    (a:A) (n:positive) (k:C -> A -> A) (c:C)
    {struct n} : A :=
    let twice a' n' :=
      pos_foldr_k'' (fun C (n':positive) (a':A) (k':C -> A -> A) (c:C) =>
                       f (xI n') a' force_eta $ fun _ a' =>
                         f (xO n') a' force_eta $ fun _ a' =>
                           k' c a')
                    a'
                    n'
                    force_eta
                    (fun _ a' =>
                       f xH a' force_eta $ fun _ a' =>
                         k c a')
    in
    match n with
    | xH => k c a
    | xO n' => twice a n'
    | xI n' => f (xO n') a force_eta $ fun _ a =>
                 twice a n'
    end.
Definition pos_foldr_k' {A C}
    (f:forall {C}, positive -> A -> (C -> A -> A) -> C -> A)
    (a:A) (n:positive) (k:C -> A -> A) (c:C) : A :=
  f n a force_eta $ fun _ a =>
    pos_foldr_k'' (@f) a n k c.
Definition pos_foldr_k {A} (f:forall {C}, positive -> (C -> A) -> C -> A) (a:A) (n:positive) : A :=
  pos_foldr_k' (fun C n (a:A) (k:C -> A -> A) (c:C) =>
                  k c (f n id a))
               a n force_eta (const id).
Definition pos_foldr_k2 {A} (f:forall {C}, positive -> (C -> A) -> C -> A) (a:A) (n:positive) : A :=
  pos_foldr_k' (fun C n (a:A) (k:C -> A -> A) (c:C) =>
                  f n (fun c => k c a) c)
               a n force_eta (const id).
Definition pos_iterr_k {A} (f:forall {B}, (B -> A) -> B -> A) : A -> positive -> A :=
  pos_foldr_k $ fun _ => const f.

Require Import Monad.
Import MonadNotation.

Definition medium : positive := 10000%positive.
Definition large : positive := 100000%positive.
Definition larger : positive := 10000000%positive.

Eval compute in pos_foldr cons nil 20%positive.
Eval compute in pos_foldr2 cons nil 20%positive.
Eval compute in pos_foldl_k (fun _ n k b => cons n (k b)) nil 20%positive.
Eval compute in pos_foldr_k (fun _ n k b => cons n (k b)) nil 20%positive.
Eval compute in pos_foldr_k2 (fun _ n k b => cons n (k b)) nil 20%positive.

Time Eval compute in pos_foldr (fun _ n => n + 1%positive) 1%positive large.
Time Eval compute in pos_foldl (fun _ n => n + 1%positive) 1%positive large.
Time Eval compute in pos_foldr2 (fun _ n => n + 1%positive) 1%positive large.
Time Eval compute in pos_foldr' (fun _ _ n k => k (n + 1%positive)) 1%positive large id.
Time Eval compute in pos_foldl_k (fun _ _ k b => k b + 1%positive) 1%positive medium.
Time Eval compute in pos_foldr_k (fun _ _ k b => k b + 1%positive) 1%positive large.
Time Eval compute in pos_foldr_k2(fun _ _ k b => k b + 1%positive) 1%positive large.

Definition mfix1 {A B} (ff: (A -> option B) -> A -> option B) (a:A) (n:positive) : option B :=
  pos_iterl ff (fun _ => None) n a.

Definition mfix2 {A B} (ff: (A -> option B) -> A -> option B) (a:A) (n:positive) : option B :=
  pos_iterl_k (fun _ k b a => ff (k b) a) (fun _ => None) n a.

Definition mfix3 {A B} (ff: (A -> option B) -> A -> option B) (a:A) (n:positive) : option B :=
  pos_iterr ff (fun _ => None) n a.

Definition mfix4 {A B} (ff: (A -> option B) -> A -> option B) (a:A) (n:positive) : option B :=
  pos_iterr_k (fun _ k b a => ff (k b) a) (fun _ => None) n a.

(*
Require Import Structures.EqDec.
Require Import Structures.Functor.
Require Import Data.Option.

Import EqDecNotation.

Definition ffact
    (mfix:forall {A B}, ((A -> option B) -> A -> option B) -> A -> positive -> option B)
    (fuel:positive) (n:positive) : option positive :=
  mfix (fun ffact n =>
    if n '=! 1%positive then Some n else
      fmap (times n) $ ffact (BinPosDef.Pos.sub n 1%positive)) n fuel.

Eval compute in ffact (@mfix4) larger 10%positive.
  
*)
*)
*)