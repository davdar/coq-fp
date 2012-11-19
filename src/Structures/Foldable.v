Require Import Data.Identity.
Require Import Data.Susp.
Require Import Structures.Comonad.
Require Import Structures.Monad.
Require Import Data.FunctionPre.
Require Import Data.Cont.
Require Import Structures.MonadCont.

Import MonadNotation.
Import FunctionNotation.
Import SuspNotation.

Definition Cofold m A T {B} := (A -> m B -> B) -> m B -> T -> B.

Definition flip_cofold {m A T B}
  (cofold:(m B -> A -> B) -> m B -> T -> B) : Cofold m A T := cofold <.> flip.

Definition unflip_cofold {m A T B}
  (flipped:(A -> m B -> B) -> m B -> T -> B)
  : (m B -> A -> B) -> m B -> T -> B := flipped <.> flip.

Definition unflip_fold {A T B}
  (flipped:(A -> B -> B) -> B -> T -> B)
  : (B -> A -> B) -> B -> T -> B := flipped <.> flip.

Definition unflip_mfold {m A T B}
  (flipped:(A -> B -> m B) -> B -> T -> m B)
  : (B -> A -> m B) -> B -> T -> m B := flipped <.> flip.

Definition unflip_lazyfold {A T B}
    (flipped:(forall {C}, A -> (C -> B) -> C -> B) -> B -> T -> B)
    : (forall {C}, (C -> B) -> C -> A -> B) -> B -> T -> B :=
  fun f =>
    flipped $ fun _ a k l => f _ k l a.

Definition mk_fold {A T B} (cofold:Cofold identity A T)
    (f:A -> B -> B) (b:B) : T -> B :=
  cofold (fun (a:A) (bM:identity B) => f a $ run_identity bM) (Identity b).

Definition mk_mfold {m} {M:Monad m} {A T B} (cofold:Cofold identity A T)
    (f:A -> B -> m B) (b:B) : T -> m B :=
  mk_fold cofold (fun (a:A) (bM:m B) => b <- bM ;; f a b) (ret b).

Definition mk_revfold {A T B} (cofold:Cofold identity A T)
    (f:A -> B -> B) : B -> T -> B :=
  run_cont <..> 
    mk_mfold cofold (fun (a:A) (b:B) =>
                       callcc $ fun (k:B -> cont B B) =>
                         b <- k b ;;
                         ret $ f a b).

Definition mk_lazyfold {A T B} (cofold:Cofold susp A T)
    (f:forall {C}, A -> (C -> B) -> C -> B) (b:B) : T -> B :=
  cofold (fun (a:A) (bM:susp B) => f a force bM) (delay | b).

Class FoldableR A T :=
  { cofoldr : forall {m} {M:Comonad m} {B}, (A -> m B -> B) -> m B -> T -> B }.

Definition foldr {T A} {F:FoldableR A T} {B}
  : (A -> B -> B) -> B -> T -> B := mk_fold cofoldr.

Definition mfoldr {T A} {F:FoldableR A T} {m} {M:Monad m} {B}
  : (A -> B -> m B) -> B -> T -> m B := mk_mfold cofoldr.

Definition revfoldr {T A} {F:FoldableR A T} {B}
  : (A -> B -> B) -> B -> T -> B := mk_revfold cofoldr.
  
Definition lazyfoldr {T A} {F:FoldableR A T} {B}
  : (forall {C}, A -> (C -> B) -> C -> B) -> B -> T -> B := mk_lazyfold cofoldr.

Definition fold_fix {T A B} {F:FoldableR T T}
    (ff:(T -> A -> option B) -> T -> A -> option B) (t:T) (a:A) : option B :=
  lazyfoldr (fun _ a k l => ff $ fun _ b => k l a b) (const2 None) t t a.

Definition fold_mfix {m} {M:Monad m} {T A B} {F:FoldableR T T}
    (ff:(T -> A -> m (option B)) -> T -> A -> m (option B)) (t:T) (a:A) : m (option B) :=
  lazyfoldr (fun _ a k l => ff $ fun _ b => k l a b) (const2 $ ret None) t t a.

Class FoldableL A T :=
  { cofoldl : forall {m} {M:Comonad m} {B}, (m B -> A -> B) -> m B -> T -> B }.

Definition foldl {T A} {F:FoldableL A T} {B}
  : (B -> A -> B) -> B -> T -> B := unflip_fold $ mk_fold $ flip_cofold cofoldl.

Definition mfoldl {T A} {F:FoldableL A T} {m} {M:Monad m} {B}
  : (B -> A -> m B) -> B -> T -> m B := unflip_mfold $ mk_mfold $ flip_cofold cofoldl.

Definition revfoldl {T A} {F:FoldableL A T} {B}
  : (B -> A -> B) -> B -> T -> B := unflip_fold $ mk_revfold $ flip_cofold cofoldl.
  
Definition lazyfoldl {t A} {F:FoldableL A t} {B}
    : (forall {C}, (C -> B) -> C -> A -> B) -> B -> t -> B :=
  unflip_lazyfold $ mk_lazyfold $ flip_cofold cofoldl.

