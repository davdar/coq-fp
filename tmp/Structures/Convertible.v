Class Convertible A B :=
  { convert : A -> B }.

Definition convert_to {A} B {Conv:Convertible A B} : A -> B := convert.
Definition convert_from A {B} {Conv:Convertible A B} : A -> B := convert.