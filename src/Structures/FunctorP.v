Require Import FP.Structures.Proxy.

Class FMapP (P:Type->Type) (t:Type->Type) : Type :=
  { fmap_p : forall {A B} {p:Px (P B)}, (A -> B) -> t A -> t B }.