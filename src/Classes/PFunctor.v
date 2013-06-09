Class PFunctor (t:Type->Type) :=
  { pfret : forall {A}, A -> t A
  ; pfmap : forall {A B}, (A -> B) -> t A -> t B
  }.