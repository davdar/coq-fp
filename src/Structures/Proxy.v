
Class Proxy (P:Type) := { proxy : P }.
Arguments proxy {P} Proxy.
Class Proxy2 (P:Type->Type) (T:Type) : Type := { proxy2 : P T }.
Arguments proxy2 {P T} Proxy2.
Class Proxy3 (P:Type->Type->Type) (T:Type) (U:Type) : Type := { proxy3 : P T U }.
Arguments proxy3 {P T U} Proxy3.