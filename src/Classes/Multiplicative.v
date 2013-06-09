Class Times T := { times : T -> T -> T }.
Class One T := { one : T }.
Class Div T := { div : T -> T -> T }.
Class Inv T := { inv : T -> T }.

Module MultiplicativeNotation.
  Infix "*" := times.
  Infix "/" := div.
End MultiplicativeNotation.