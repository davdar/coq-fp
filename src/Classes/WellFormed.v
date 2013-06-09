Class WellFormed T := { wf : T -> Prop }.

Definition with_wf (T:Type) `{! WellFormed T } : Type := { t:T | wf t }.