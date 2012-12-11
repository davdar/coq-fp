Require Import FP.Data.Function.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadTrans.
Require Import FP.Structures.Functor.

Import FunctionNotation.
Import MonadNotation.
Import FunctorNotation.

Class Continuation m :=
  { callcc : forall {A}, (forall {R}, (A -> m R) -> m R) -> m A }.

Inductive kon_t (m:Type->Type) A := KonT { un_kon_t : forall {R}, (A -> m R) -> m R }.
Arguments KonT {m A} _.
Arguments un_kon_t {m A} _ {R} _.

Definition run_kon_t {m} {M:Monad m} {A} (aMK:kon_t m A) : m A := un_kon_t aMK ret.

Instance kon_Monad {m} {M:Monad m} : Monad (kon_t m) :=
  { ret :=
      fun A (a:A) =>
        KonT $ fun R (k:A -> m R) =>
          k a
  ; bind :=
      fun A B (aMK:kon_t m A) (f:A -> kon_t m B) =>
        KonT $ fun R (k:B -> m R) =>
          un_kon_t aMK $ fun (a:A) => 
            k =<< run_kon_t (f a)
  }.

Instance kon_MonadTrans : MonadTrans kon_t :=
  { lift :=
      fun m M A (aM:m A) =>
        KonT $ fun R (k:A -> m R) =>
          aM >>= k
  }.

Instance kon_Continuation {m} {M:Monad m} : Continuation (kon_t m) :=
  { callcc :=
      fun A (kk:forall {R}, (A -> kon_t m R) -> kon_t m R) =>
        KonT $ fun R (k:A -> m R) =>
          run_kon_t $ kk $ lift '.' k
  }.

Class Cont3 m :=
  { callcc3 : forall {A R}, ((A -> m R R) -> m R R) -> m R A }.

Inductive kon_t3 (m:Type->Type) R A := KonT3 { un_kon_t3 : (A -> m R) -> m R }.
Arguments KonT3 {m R A} _.
Arguments un_kon_t3 {m R A} _ _.

Definition kon_t3_lift {m} {M:Monad m} {A} (aM:m A) : kon_t3 m A A :=
  KonT3 $ fun (k:A -> m A) => aM >>= k.

Instance kon_Monad3 {m} {M:Monad m} {R} : Monad (kon_t3 m R) :=
  { ret :=
      fun A (a:A) =>
        KonT3 $ fun (k:A -> m R) =>
          k a
  ; bind :=
      fun A B (aMK:kon_t3 m R A) (f:A -> kon_t3 m R B) =>
        KonT3 $ fun (k:B -> m R) =>
          un_kon_t3 aMK $ fun (a:A) =>
            un_kon_t3 (f a) k
  }.

Instance kon_Cont3 {m} {M:Monad m} : Cont3 (kon_t3 m) :=
  { callcc3 :=
      fun A R (kk:(A -> kon_t3 m R R) -> kon_t3 m R R) =>
        KonT3 $ fun (k:A -> m R) =>
          un_kon_t3 (kk (kon_t3_lift '.' k)) ret
  }.
  

Inductive reader_tk E (m:Type->Type->Type) R A := ReaderTK { un_reader_tk : E -> m R A }.
Arguments ReaderTK {E m R A} _.
Arguments un_reader_tk {E m R A} _ _.

Definition run_reader_tk {E m R A} e (x:reader_tk E m R A) := un_reader_tk x e.

Instance Rasdfa {m} {M:forall R, Monad (m R)} {C:Cont3 m} {E} : Cont3 (reader_tk E m) :=
  { callcc3 :=
      fun A R (kk:(A -> reader_tk E m R R) -> reader_tk E m R R) =>
        ReaderTK $ fun (e:E) =>
          callcc3 $ fun (k:A -> m R R) =>
            run_reader_tk e $
              kk $ fun (a:A) =>
                ReaderTK (fun _ => k a)
  }.
  
Class Cont R m :=
  { callcc' : forall {A}, (forall {R'}, (R -> m R') -> (A -> m R) -> m R') -> m A }.

Inductive kon_t' R (m:Type->Type) A := KonT' { un_kon_t' : forall {R'}, (R -> m R') -> (A -> m R) -> m R' }.
Arguments KonT' {R m A} _.
Arguments un_kon_t' {R m A} _ {R'} _ _.

Definition run_kon_t' {m} {M:Monad m} {A} (aMK:kon_t' A m A) : m A := un_kon_t' aMK ret ret.

Instance kon_Monad' {R} {m} {M:Monad m} : Monad (kon_t' R m) :=
  { ret :=
      fun A (a:A) =>
        KonT' $ fun R' (k_out:R -> m R') (k_in:A -> m R) => k_in a >>= k_out
  ; bind :=
      fun A B (aMK:kon_t' R m A) (f:A -> kon_t' R m B) =>
        KonT' $ fun R' (k_out:R -> m R') (k_in:B -> m R) =>
          un_kon_t' aMK k_out $ fun (a:A) =>
            un_kon_t' (f a) ret k_in
}.

Instance kon_MonadTrans' {R} : MonadTrans (kon_t' R) :=
  { lift :=
      fun m M A (aM:m A) =>
        KonT' $ fun R' (k_out:R -> m R') (k_in:A -> m R) =>
          aM >>= k_in >>= k_out
  }.

Instance kon_Cont {R} {m} {M:Monad m} : Cont R (kon_t' R m) :=
  { callcc' :=
      fun A (kk:forall {R'}, (R -> kon_t' R m R') -> (A -> kon_t' R m R) -> kon_t' R m R') =>
        KonT' $ fun R' (k_out:R -> m R') (k_in:A -> m R) =>
          un_kon_t' (kk ret (lift '.' k_in)) k_out ret
  }.

Class Cont2 m :=
  { callcc2 : forall {R A}, (forall {R'}, (R -> m R R') -> (A -> m R R) -> m R R') -> m R A
  ; map_kont : forall {R R' A}, (R -> R') -> (R' -> R) -> m R A -> m R' A
  }.

Inductive kon_t2 (m:Type -> Type) R A := KonT2 { un_kon_t2 : forall {R'}, (R -> m R') -> (A -> m R) -> m R' }.
Arguments KonT2 {m R A} _.
Arguments un_kon_t2 {m R A} _ {R'} _ _.

Definition run_kon_t2 {m} {M:Monad m} {A} (aMK:kon_t2 m A A) : m A := un_kon_t2 aMK ret ret.
Definition lift_kon_t2 {m} {M:Monad m} {A} (aM:m A) : kon_t2 m A A :=
  KonT2 $ fun R' k_out k_in => aM >>= k_in >>= k_out.

Instance kon_Monad2 {m} {M:Monad m} {R} : Monad (kon_t2 m R) :=
  { ret :=
      fun A (a:A) =>
        KonT2 $ fun R' (k_out:R -> m R') (k_in:A -> m R) => k_in a >>= k_out
  ; bind :=
      fun A B (aMK:kon_t2 m R A) (f:A -> kon_t2 m R B) =>
        KonT2 $ fun R' (k_out:R -> m R') (k_in:B -> m R) =>
          un_kon_t2 aMK k_out $ fun (a:A) =>
            un_kon_t2 (f a) ret k_in
  }.

Instance Kon_Cont2 {m} {M:Monad m} : Cont2 (kon_t2 m) :=
  { callcc2 :=
      fun R A (kk:forall {R'}, (R -> kon_t2 m R R') -> (A -> kon_t2 m R R) -> kon_t2 m R R') =>
        KonT2 $ fun R' (k_out:R -> m R') (k_in:A -> m R) =>
          un_kon_t2 (kk ret (lift_kon_t2 '.' k_in)) k_out ret
  ; map_kont :=
      fun R R' A (f:R -> R') (g:R' -> R) (aMK:kon_t2 m R A) =>
        KonT2 $ fun R'' (k_out:R' -> m R'') (k_in:A -> m R') =>
          un_kon_t2 aMK _ _
  }.
Admitted.

