Class MFix (m:Type->Type) : Type :=
  { mfix : forall {A B:Type}, ((A -> m B) -> (A -> m B)) -> (A -> m B) }.

Definition mfix2 {m} {MFix_:MFix m} {A B C}
    (ff:(A -> B -> m C) -> A -> B -> m C) (a:A) (b:B) : m C :=
  let ff' (f:A*B -> m C) (ab:A*B) : m C :=
    let f' (a:A) (b:B) : m C := f (a,b) in 
    let (a,b) := ab in
    ff f' a b
  in mfix ff' (a,b).

Definition mfix3 {m} {MFix_:MFix m} {A B C D}
    (ff:(A -> B -> C -> m D) -> A -> B -> C -> m D) (a:A) (b:B) (c:C) : m D :=
  let ff' (f:A*B*C -> m D) (abc:A*B*C) : m D :=
    let f' (a:A) (b:B) (c:C) : m D := f (a,b,c) in 
    let '(a,b,c) := abc in
    ff f' a b c
  in mfix ff' (a,b,c).
