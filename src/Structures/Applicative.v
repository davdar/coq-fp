Require Import Structures.Pointed.

Class Applicative T :=
{ applicative_Pointed :> forall {A}, Pointed (T A)
; app : forall {A B}, T (A -> B) -> T A -> T B
}.

Module ApplicativeNotation.
  Infix "<*>" := app (at level 45, right associativity).
End ApplicativeNotation.

