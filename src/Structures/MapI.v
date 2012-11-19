Require Import Data.Function.
Require Import Data.List.
Require Import Data.Prod.
Require Import Data.N.
Require Import Structures.Functor.
Require Import Structures.FunctorP.
Require Import Structures.Monoid.

Import FunctionNotation.

Class MapI K t :=
  { map_Functor :> Functor t
  ; mempty : forall {V}, t V 
  ; msingleton : forall {V}, K -> V -> t V
  ; mlookup : forall {V}, K -> t V -> option V
  ; minsert_with : forall {V}, (V -> V -> V) -> K -> V -> t V -> t V
  ; mremove : forall {V}, K -> t V -> t V * option V
  ; mupdate : forall {V}, K -> (V -> V) -> t V -> t V
  ; munionl : forall {V}, t V -> t V -> t V
  ; mdifference : forall {V W}, t V -> t W -> t V
  ; mintersect_with : forall {V W X}, (V -> W -> X) -> t V -> t W -> t X
  ; mmap_with : forall {V W}, (K -> V -> W) -> t V -> t W
  }.

Section MapI.
  Context {t K} {M:MapI K t} {V:Type}.

  Definition minsertl : K -> V -> t V -> t V := minsert_with const.
  Definition minsertr : K -> V -> t V -> t V := minsert_with (const id).
  Definition munionr : t V -> t V -> t V := flip munionl.
  Definition munionsl : list (t V) -> t V := foldr munionl mempty.
  Definition munionsr : list (t V) -> t V := foldr munionr mempty.
End MapI.

Class FiniteMapI K t :=
  { finite_map_MapI :> MapI K t
  ; msize : forall {V}, t V -> N
  ; mreduce : forall {V} {M:Monoid V}, t V -> V
  ; mfrom_list : forall {V}, list (K*V) -> t V
  ; mto_list : forall {V}, t V -> list (K*V)
  }.

Class SetI P t :=
  { set_Functor :> FunctorP P t
  ; sempty : forall {E} {p:P E}, t E
  ; ssingleton : forall {E} {p:P E}, E -> t E
  ; smember : forall {E} {p:P E}, E -> t E -> bool
  ; sinsert : forall {E} {p:P E}, E -> t E -> t E
  ; sremove : forall {E} {p:P E}, E -> t E -> t E * bool
  ; sunionl : forall {E} {p:P E}, t E -> t E -> t E
  ; sdifference : forall {E} {p:P E}, t E -> t E -> t E
  ; sintersect : forall {E} {p:P E}, t E -> t E -> t E
  }.

Section SetI.
  Context {t P} {S:SetI P t} {E} {p:P E}.
  Definition sunionr : t E -> t E -> t E := flip $ sunionl (p:=p).
  Definition sunionsl : list (t E) -> t E := foldr (sunionl (p:=p)) (sempty (p:=p)).
  Definition sunionsr : list (t E) -> t E := foldr sunionr (sempty (p:=p)).
End SetI.

Class FiniteSetI P t :=
  { finite_set_SetI :> SetI P t
  ; ssize : forall {E} {p:P E}, t E -> N
  ; sreduce : forall {E} {p:P E} {M:Monoid E}, t E -> E
  ; sfrom_list : forall {E} {p:P E}, list E -> t E
  ; sto_list : forall {E} {p:P E}, t E -> list E
  }.

