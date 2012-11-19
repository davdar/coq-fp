Require Import Monoid.

Class Semimultiplicative t :=
  { Semimultiplicative_Semigroup : Semigroup t }.
Definition times {t} {M:Semimultiplicative t} : t -> t -> t :=
  gtimes (Semigroup:=Semimultiplicative_Semigroup).

Class Multiplicative t :=
  { Multiplicative_Monoid : Monoid t }.
Definition one {t} {M:Multiplicative t} : t :=
  gunit (Monoid:=Multiplicative_Monoid).
Instance Multiplicative_Semimultiplicative {t} {M:Multiplicative t} : Semimultiplicative t :=
  { Semimultiplicative_Semigroup :=
      Monoid_Semigroup (Monoid:=Multiplicative_Monoid)
  }.

Class InverseMultiplicative t :=
  { InverseMultiplicative_InverseMonoid : InverseMonoid t }.
Definition inv {t} {IM:InverseMultiplicative t} : t -> t :=
  ginv (InverseMonoid:=InverseMultiplicative_InverseMonoid).
Definition div {t} {IM:InverseMultiplicative t} : t -> t -> t :=
  gdiv (InverseMonoid:=InverseMultiplicative_InverseMonoid).
Instance InverseMultiplicative_Multiplicative
    {t} {IM:InverseMultiplicative t} : Multiplicative t :=
  { Multiplicative_Monoid :=
      InverseMonoid_Monoid (InverseMonoid:=InverseMultiplicative_InverseMonoid)
  }.


Module MultiplicativeNotation.
  Infix "*" := times.
  Infix "/" := div.
End MultiplicativeNotation.
