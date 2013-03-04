Require Import FP.Data.Function.
Require Import FP.Data.List.
Require Import FP.Data.Prod.
Require Import FP.Data.N.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.FunctorP.
Require Import FP.Structures.Monoid.

Import FunctionNotation.

Class MapI K t :=
  { mempty : forall {V}, t V 
  ; msingleton : forall {V}, K -> V -> t V
  ; mlookup : forall {V}, K -> t V -> option V
  ; minsert_with : forall {V}, (V -> V -> V) -> K -> V -> t V -> t V
  ; mremove : forall {V}, K -> t V -> t V * option V
  ; mupdate : forall {V}, K -> (V -> V) -> t V -> t V
  ; munion_with : forall {V}, (V -> V -> V) -> t V -> t V -> t V
  ; mdifference : forall {V W}, t V -> t W -> t V
  ; mintersect_with : forall {V W X}, (V -> W -> X) -> t V -> t W -> t X
  ; mmap_with : forall {V W}, (K -> V -> W) -> t V -> t W
  }.

Section MapI.
  Context {t K} {M:MapI K t} {V:Type}.

  Definition minsertl : K -> V -> t V -> t V := minsert_with const.
  Definition minsertr : K -> V -> t V -> t V := minsert_with (const id).
  Definition munionl : t V -> t V -> t V := munion_with const.
  Definition munionr : t V -> t V -> t V := munion_with (const id).
  Definition munions_with (f:V -> V -> V) : list (t V) -> t V := foldr (munion_with f) mempty.
  Definition munionsl : list (t V) -> t V := munions_with const.
  Definition munionsr : list (t V) -> t V := foldr munionr mempty.
End MapI.

Class FiniteMapI K t :=
  { msize : forall {V}, t V -> N
  ; mreduce : forall {V} {M:Monoid V}, t V -> V
  ; mfrom_list : forall {V}, list (K*V) -> t V
  ; mto_list : forall {V}, t V -> list (K*V)
  }.

Class SetI P t :=
  { sempty : forall {E} {p:Proxy2 P E}, t E
  ; ssingleton : forall {E} {p:Proxy2 P E}, E -> t E
  ; smember : forall {E} {p:Proxy2 P E}, E -> t E -> bool
  ; sinsert : forall {E} {p:Proxy2 P E}, E -> t E -> t E
  ; sremove : forall {E} {p:Proxy2 P E}, E -> t E -> t E * bool
  ; sunionl : forall {E} {p:Proxy2 P E}, t E -> t E -> t E
  ; sdifference : forall {E} {p:Proxy2 P E}, t E -> t E -> t E
  ; sintersect : forall {E} {p:Proxy2 P E}, t E -> t E -> t E
  }.

Section SetI.
  Context {t P} {S:SetI P t} {E} {p:Proxy2 P E}.
  Definition sunionr : t E -> t E -> t E := flip $ sunionl .
  Definition sunionsl : list (t E) -> t E := foldr sunionl sempty.
  Definition sunionsr : list (t E) -> t E := foldr sunionr sempty.
End SetI.

Class FiniteSetI P t :=
  { ssize : forall {E} {p:Proxy2 P E}, t E -> N
  ; sreduce : forall {E} {p:Proxy2 P E} {M:Monoid E}, t E -> E
  ; sfrom_list : forall {E} {p:Proxy2 P E}, list E -> t E
  ; sto_list : forall {E} {p:Proxy2 P E}, t E -> list E
  }.