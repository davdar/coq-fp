Require Import FP.CoreClasses.

Import CoreClassesNotation.

Class GTimes T := { gtimes : T -> T -> T }.
Class GUnit T := { gunit : T }.
Class GDiv T := { gdiv : T -> T -> T }.
Class GInv T := { ginv : T -> T }.

Module MonoidNotation.
  Infix "**" := gtimes (at level 46, right associativity).
  Infix "//" := gdiv (at level 45, right associativity).
End MonoidNotation.
Import MonoidNotation.

Definition div_from_inv {T} (times:T -> T -> T) (inv:T -> T) (t1:T) (t2:T) : T :=
  times t1 (inv t2).

Class Semigroup T `{! Eqv T ,! GTimes T } :=
  { semigroup_associativity : forall {x y z}, (x ** y) ** z ~= x ** y ** z }.

Class CommutativeSemigroup T `{! Eqv T ,! GTimes T } :=
  { commutative_semigroup_semigroup :> Semigroup T
  ; commutative_semigroup_commutativity : forall {x y}, x ** y ~= y ** x
  }.

Class MonoidUnit T `{! Eqv T ,! GTimes T ,! GUnit T } :=
  { monoid_unit_left : forall {x}, gunit ** x ~= x
  ; monoid_unit_right : forall {x}, x ** gunit ~= x
  }.

Class Monoid T `{! Eqv T ,! GTimes T ,! GUnit T } :=
  { monoid_semigroup :> Semigroup T
  ; monoid_monoid_unit :> MonoidUnit T
  }.

Class CommutativeMonoid T `{! Eqv T ,! GTimes T ,! GUnit T } :=
  { commutative_monoid_commutative_semigroup :> CommutativeSemigroup T
  ; commutative_monoid_monoid_unit :> MonoidUnit T
  }.

Class GroupInverse T `{! Eqv T ,! GTimes T ,! GUnit T ,! GDiv T ,! GInv T } :=
  { group_inverse_left : forall {x}, ginv x ** x ~= gunit
  ; group_inverse_right : forall {x}, x ** ginv x ~= gunit
  ; group_inverse_div : forall {x}, gunit // x ~= ginv x
  }.

Class Group T `{! Eqv T ,! GTimes T ,! GUnit T ,! GDiv T ,! GInv T }:=
  { group_moniod :> Monoid T
  ; group_group_inverse :> GroupInverse T
  }.

Class AlbelianGroup T `{! Eqv T ,! GTimes T ,! GUnit T ,! GDiv T ,! GInv T } :=
  { albelian_group_commutative_monoid :> CommutativeMonoid T
  ; albelian_group_group_inverse :> GroupInverse T
  }.