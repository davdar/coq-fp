Require Import FP.Categories.

Instance Plus_Set : Plus Set := { plus_gtimes := {| gtimes := sum:Set->Set->Set |} }.
Instance Zero_Set : One Set := { one_gunit := {| gunit := Empty_set |} }.
Instance Times_Set : Times Set := { times_gtimes := {| gtimes := prod:Set->Set->Set |} }.
Instance One_Set : One Set := { one_gunit := {| gunit := unit |} }.

Instance Plus_Type : Plus Type := { plus_gtimes := {| gtimes := sum |} }.
Instance Zero_Type : Zero Type := { zero_gunit := {| gunit := Empty_set:Type |} }.
Instance Times_Type : Times Type := { times_gtimes := {| gtimes := prod |} }.
Instance One_Type : One Type := { one_gunit := {| gunit := unit:Type |} }.
