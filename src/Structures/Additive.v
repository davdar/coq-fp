Require Import Structures.Monoid.

Class Semiadditive t :=
  { Semiadditive_Semigroup : Semigroup t }.
Definition plus {t} {A:Semiadditive t} : t -> t -> t :=
  gtimes (Semigroup:=Semiadditive_Semigroup).

Class Additive t :=
  { Additive_Monoid : Monoid t }.
Definition zero {t} {A:Additive t} : t :=
  gunit (Monoid:=Additive_Monoid).
Instance Additive_Semiadditive {t} {A:Additive t} : Semiadditive t :=
  { Semiadditive_Semigroup :=
      Monoid_Semigroup (Monoid:=Additive_Monoid)
  }.

Class InverseAdditive t :=
  { InverseAdditive_InverseMonoid : InverseMonoid t }.
Definition neg {t} {IA:InverseAdditive t} : t -> t :=
  ginv (InverseMonoid:=InverseAdditive_InverseMonoid).
Definition minus {t} {IA:InverseAdditive t} : t -> t -> t :=
  gdiv (InverseMonoid:=InverseAdditive_InverseMonoid).
Instance InverseAdditive_Additive {t} {IA:InverseAdditive t} : Additive t :=
  { Additive_Monoid :=
      InverseMonoid_Monoid (InverseMonoid:=InverseAdditive_InverseMonoid)
  }.

Module AdditiveNotation.
  Infix "+" := plus.
  Infix "-" := minus.
End AdditiveNotation.
