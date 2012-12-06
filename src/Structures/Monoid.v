Class GTimes T :=
  { gtimes : T -> T -> T }.
Class GUnit T :=
  { gunit : T }.
Class GDiv T :=
  { gdiv : T -> T -> T }.
Class GInv T :=
  { ginv : T -> T }.

Module MonoidNotation.
  Infix "**" := gtimes (at level 45, right associativity).
  Infix "//" := gdiv (at level 45, right associativity).
End MonoidNotation.
Import MonoidNotation.

Section Groupish.
  Context {T} {T_GTimes : GTimes T} {T_GInv : GInv T}.
  Definition gdiv_from_inv (t1:T) (t2:T) : T :=
    t1 ** ginv t2.
End Groupish.

Class Semigroup T :=
  { semigroup_times : T -> T -> T }.
Section Semigroup.
  Context {T} {T_Semigroup : Semigroup T}.
  Global Instance Semigroup_GTimes : GTimes T :=
    { gtimes := semigroup_times }.
End Semigroup.
Class DivSemigroup T :=
  { div_semigroup_times : T -> T -> T
  ; div_semigroup_div : T -> T -> T
  }.
Section DivSemigroup.
  Context {T} {T_DivSemigroup : DivSemigroup T}.
  Global Instance DivSemigroup_Semigroup : Semigroup T :=
    { semigroup_times := div_semigroup_times }.
  Global Instance DivSemigroup_GDiv : GDiv T :=
    { gdiv := div_semigroup_div }.
End DivSemigroup.

Class Monoid t :=
  { monoid_unit : t
  ; monoid_times : t -> t -> t
  }.
Section Monoid.
  Context {T} {T_Monoid : Monoid T}.
  Global Instance Monoid_Semigroup : Semigroup T :=
    { semigroup_times := monoid_times }.
  Global Instance Monoid_GUnit : GUnit T :=
    { gunit := monoid_unit }.
End Monoid.
Class InvMonoid t :=
  { inv_monoid_unit : t
  ; inv_monoid_times : t -> t -> t
  ; inv_monoid_inv : t -> t
  }.
Section InvMonoid.
  Context {T} {T_InverseMonoid : InvMonoid T}.
  Global Instance InvMonoid_Monoid : Monoid T :=
    { monoid_unit := inv_monoid_unit
    ; monoid_times := inv_monoid_times
    }.
  Global Instance InvMonoid_GInv : GInv T :=
    { ginv := inv_monoid_inv }.
  Global Instance InvMonoid_GDiv : GDiv T :=
    { gdiv := gdiv_from_inv }.
End InvMonoid.
                                      
