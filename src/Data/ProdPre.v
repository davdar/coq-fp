Arguments fst {A B} _.
Arguments snd {A B} _.

Definition firstf {A B C} (f:A -> C) (p:A*B) : C*B :=
  let (a,b) := p in (f a,b).

Definition secondf {A B C} (f:B -> C) (p:A*B) : A*C :=
  let (a,b) := p in (a, f b).
