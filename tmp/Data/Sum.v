Section notation.
  Local Infix "+" := sum.

  Definition collapse {A} (a:A+A) : A := match a with inl x => x | inr x => x end.

  Inductive sum_t A m B := SumT { un_sum_t : m (A+B) }.

  Definition sum_associate {A B C} (x:A+(B+C)) : (A+B)+C :=
    match x with
    | inl a => inl (inl a)
    | inr (inl b) => inl (inr b)
    | inr (inr c) => inr c
    end.
End notation.
Arguments SumT {A m B} un_sum_t.
Arguments un_sum_t {A m B} _.
