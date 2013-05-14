Require Import FP.CoreData.
Require Import FP.Categories.

Import CategoriesNotation.
Import CoreDataNotation.

Fixpoint pos_cofold' {w} `{! Counit w ,! Cobind w } {A}
    (f:positive -> w A -> A) (aW:w A) (n:positive) : A :=
  let double_cofold :=
    pos_cofold' $ fun n aW =>
      let aW := codo aW => f (xI n) aW in
      f (xO n) aW
  in
  match n with
  | xH => coret aW
  | xO n =>
      let aW := codo aW => double_cofold aW n in
      f xH aW
  | xI n =>
      let aW := codo aW => f (xO n) aW in
      let aW := codo aW => double_cofold aW n in
      f xH aW
  end.
Definition pos_cofold {w} `{! Counit w ,! Cobind w } {A}
    (f:positive -> w A -> A) (aW:w A) (n:positive) : A :=
  let aW := codo aW => f n aW in
  pos_cofold' f aW n.
Instance pos_Foldable : Foldable positive positive :=
  { cofold := @pos_cofold }.

Fixpoint pos_coiter' {w} `{! Counit w ,! Cobind w } {A}
    (f:w A -> positive -> A) (aW:w A) (n:positive) : A :=
  let double_cofold :=
    pos_coiter' $ fun aW n =>
      let aW := codo aW => f aW (xO n) in
      f aW (xI n)
  in
  match n with
  | xH => coret aW
  | xO n =>
      let aW := codo aW => f aW xH in
      double_cofold aW n
  | xI n =>
      let aW := codo aW => f aW xH in
      let aW := codo aW => double_cofold aW n in
      f aW (xO n)
  end.
Definition pos_coiter {w} `{! Counit w ,! Cobind w } {A}
    (f:w A -> positive -> A) (aW:w A) (n:positive) : A :=
  let aW := codo aW => pos_coiter' f aW n in
  f aW n.
Instance pos_Iterable : Iterable positive positive :=
  { coiter := @pos_coiter }.

Fixpoint pos_coloopr' {w} `{! Counit w ,! Cobind w } {A}
    (f:w A -> A) (aW:w A) (n:positive) : A :=
  let double_coloopr :=
    pos_coloopr' $ fun aW =>
      let aW := codo aW => f aW in
      f aW
  in
  match n with
  | xH => coret aW
  | xO n =>
      let aW := codo aW => double_coloopr aW n in
      f aW
  | xI n =>
      let aW := codo aW => double_coloopr aW n in
      let aW := codo aW => f aW in
      f aW
  end.
Definition pos_coloopr {w} `{! Counit w ,! Cobind w } {A}
    (f:w A -> A) (aW:w A) (n:positive) : A :=
  let aW := codo aW => pos_coloopr' f aW n in
  f aW.

Fixpoint pos_coloopl' {w} `{! Counit w ,! Cobind w } {A}
    (f:w A -> A) (aW:w A) (n:positive) : A :=
  let double_coloopl :=
    pos_coloopl' $ fun aW =>
      let aW := codo aW => f aW in
      f aW
  in
  match n with
  | xH => coret aW
  | xO n =>
      let aW := codo aW => f aW in
      double_coloopl aW n
  | xI n =>
      let aW := codo aW => f aW in
      let aW := codo aW => f aW in
      double_coloopl aW n
  end.
Definition pos_coloopl {w} `{! Counit w ,! Cobind w } {A}
    (f:w A -> A) (aW:w A) (n:positive) : A :=
  let aW := codo aW => f aW in
  pos_coloopl' f aW n.
Instance pos_Peano : Peano positive :=
  { pzero := xH
  ; psucc := BinPos.Pos.succ
  ; coloopr := @pos_coloopr
  ; coloopl := @pos_coloopl
  }.