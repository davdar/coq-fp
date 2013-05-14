Require Import FP.Categories.
Require Import FP.Data.Foldable.

Section Monoid.
  Context {T} `{! GTimes T ,! GUnit T }.
  Context {U} `{! Iterable T U }.

  Definition gproduct : U -> T := iter gtimes gunit.
End Monoid.
