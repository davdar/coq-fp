Require Import FP.Data.Function.
Require Import FP.Data.List.
Require Import FP.Data.Option.
Require Import FP.Structures.Alternative.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Functor.
Require Import FP.Structures.MonadFix.

Import AlternativeNotation.
Import ApplicativeNotation.
Import FunctionNotation.
Import FunctorNotation.
Import ListNotation.

Class LLParser T p :=
  { ll_parser_Applicative :> Applicative p
  ; ll_parser_Alternative :> Alternative p
  ; parse_refine : forall {A}, (T -> option A) -> p A
  }.

Section LLParser.
  Context {p T} {pP:LLParser T p}.

  Context {tE:EqvDec T}.

  Context {MF:MonadFix p}.

  Definition parse_predicate (f:T -> bool) : p T :=
    parse_refine (fun x => if f x then Some x else None).
  Definition parse_token (t:T) : p T := parse_predicate (eqv_dec t).
  Fixpoint parse_sequence (ts:list T) : p (list T) :=
    match ts with
    | nil => fret nil
    | t::ts' => cons <$> parse_token t <@> parse_sequence ts'
    end.

  Fixpoint count {A} (i:nat) (aP:p A) : p (list A) :=
    match i with
    | O => fret nil
    | S i' => cons <$> aP <@> count i' aP
    end.

  Definition optional {A} (aP:p A) : p (option A) :=
    Some <$> aP <|> fret None.

  Definition between {O C A} (open:p O) (close:p C) (aP:p A) : p A :=
    open @> aP <@ close.


  Definition many {A} : p A -> p (list A) :=
    mfix $ fun many a =>
      cons <$> a <@> many a
      <|>
      fret nil.

  Definition many1 {A} (aP:p A) : p (list A) :=
    cons <$> aP <@> many aP.

  Definition sep_by {A B} (aP:p A) (sep:p B) : p (list A) :=
    cons <$> aP <@> many (const id <$> sep <@> aP).

  Definition sep_opt_begin_by {A B} (aP:p A) (sep:p B) : p (list A) :=
    optional sep @> sep_by aP sep.

  Definition many_till {A B} : p A -> p B -> p (list A) :=
    mfix2 $ fun many_till aP nd =>
      const nil <$> nd
      <|>
      cons <$> aP <@> many_till aP nd.
End LLParser.
