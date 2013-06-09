Class Plus T := { plus : T -> T -> T }.
Arguments plus {T Plus} _ _ : simpl never.
Class Zero T := { zero : T }.
Arguments zero {T Zero} : simpl never.
Class Minus T := { minus : T -> T -> T }.
Arguments minus {T Minus} _ _ : simpl never.
Class Neg T := { neg : T -> T }.
Arguments neg {T Neg} _ : simpl never.

Module AdditiveNotation.
  Infix "+" := plus.
  Infix "-" := minus.
End AdditiveNotation.