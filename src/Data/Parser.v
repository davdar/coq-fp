Require Import Data.Ascii.
Require Import Data.Fuel.
Require Import Data.Function.
Require Import Data.List.
Require Import Data.Maps.
Require Import Data.N.
Require Import Data.Reader.
Require Import Data.String.
Require Import Data.Type.
Require Import Structures.Additive.
Require Import Structures.Alternative.
Require Import Structures.Applicative.
Require Import Structures.Convertible.
Require Import Structures.EqDec.
Require Import Structures.Functor.
Require Import Structures.LLParser.
Require Import Structures.Monad.
Require Import Structures.MonadFix.
Require Import Structures.MonadReader.
Require Import Structures.MonadTrans.
Require Import Structures.Multiplicative.
Require Import Structures.Ord.
Require Import Structures.Traversable.

Import MultiplicativeNotation.
Import EqDecNotation.
Import OrdNotation.
Import FunctionNotation.
Import FunctorNotation.
Import AlternativeNotation.
Import ApplicativeNotation.
Import MonadNotation.
Import ListNotation.
Import StringNotation.
Import AdditiveNotation.
Import CharNotation.

Inductive result (T:Type) (A:Type) :=
  | SuccessResult :
         A
      -> N (* length of input consumed *)
      -> list T
      -> result T A
  | FailResult :
         result T A.
Arguments SuccessResult {T A} _ _ _.
Arguments FailResult {T A}.

Definition result_add_length {T A} (n:N) (r:result T A) :=
  match r with
  | SuccessResult a m ts => SuccessResult a (m+n) ts
  | FailResult => FailResult
  end.

Definition result_fmap {T A B} (f:A -> B) (r:result T A) : result T B :=
  match r with
  | SuccessResult a n ts => SuccessResult (f a) n ts
  | FailResult => FailResult
  end.

Instance result_Functor {T} : Functor (result T) :=
  { fmap := @result_fmap _ }.

Inductive parser_t T m A := Parser { un_parser_t : list T -> m (result T A) }.
Arguments Parser {T m A} _.
Arguments un_parser_t {T m A} _ _.

Definition parser_lift {T m} {M:Monad m} {A} (aM:m A) : parser_t T m A :=
  Parser $ fun ts => a <- aM ;; ret $ SuccessResult a 0 ts.

Instance parser_MonadTrans {T} : MonadTrans (parser_t T) :=
  { lift := @parser_lift _ }.

Definition parser_ret {T m} {M:Monad m} {A} (a:A) : parser_t T m A :=
  lift $ ret a.

Definition parser_bind {T m} {M:Monad m} {A B} (p:parser_t T m A) (f:A -> parser_t T m B) : parser_t T m B :=
  Parser $ fun ts =>
    x <- un_parser_t p ts ;;
    match x with
    | SuccessResult a n ts' => result_add_length n <$> un_parser_t (f a) ts'
    | FailResult => ret FailResult
    end.

Instance parser_Monad {T m} {M:Monad m} : Monad (parser_t T m) :=
  { ret := @parser_ret _ _ _
  ; bind := @parser_bind _ _ _
  }.

Definition parser_zero {T m} {M:Monad m} {A} : parser_t T m A := Parser $ fun _ => ret FailResult.

Definition parser_plus {T m} {M:Monad m} {A B} (aP:parser_t T m A) (bP:parser_t T m B) : parser_t T m (A+B) :=
  Parser $ fun ts =>
    x <- un_parser_t aP ts ;;
    match x with
    | SuccessResult a n ts' => ret $ inl <$> SuccessResult a n ts'
    | FailResult => inr <$$> un_parser_t bP ts
    end.

Instance parser_Alternative {T m} {M:Monad m} : Alternative (parser_t T m) :=
  { fzero := @parser_zero _ _ _
  ; fplus := @parser_plus _ _ _
  }.

Definition parser_parse_refine {T m} {M:Monad m} {A} (f:T -> option A) : parser_t T m A :=
  Parser $ fun ts =>
    ret $
      match ts with
      | nil => FailResult
      | t::ts' =>
          match f t with
          | None => FailResult
          | Some a => SuccessResult a 1 ts'
          end
      end.

Instance parser_LLParser {T m} {M:Monad m} : LLParser T (parser_t T m) :=
  { parse_refine := @parser_parse_refine _ _ _ }.

Definition parser_fix {T m} {M:Monad m} {MF:MonadFix m} {A B}
    (ff:(A -> parser_t T m B) -> A -> parser_t T m B) (a:A) : parser_t T m B :=
  let ff' (f:A*list T -> m (result T B)) (ats:A*list T) := 
    let (a,ts) := ats in
    flip un_parser_t ts $
      flip ff a $ fun (a:A) =>
        Parser $ fun ts => f (a,ts)
  in
  Parser $ fun ts => mfix ff' (a,ts).

Instance parser_MonadFix {T m} {M:Monad m } {MF:MonadFix m}
    : MonadFix (parser_t T m) :=
  { mfix := @parser_fix _ _ _ _ }.

Definition run_parser_t {T m A} : list T -> parser_t T m A -> m (result T A) :=
  flip un_parser_t.

Definition parser T := parser_t T fuel.
Definition run_parser {T A} (n:N) (ts:list T) : parser T A -> option (result T A) :=
  run_fuel n <.> run_parser_t ts.

Fixpoint best_lex' {T A} (results:list (result T A)) : option (A * N * list T) :=
  match results with
  | [] => None
  | (FailResult::rs) => best_lex' rs
  | (SuccessResult a n ts::rs) => Some $
      match best_lex' rs with
      | None => (a, n, ts)
      | Some (a', n', ts') =>
          if n '>=! n' then
            (a, n, ts)
          else
            (a', n', ts')
      end
  end.

Definition best_lex {T A} : list (result T A) -> option (A * list T) :=
  fmap (fun x => let '(a, _, ts) := x in (a, ts)) <.> best_lex'.

Definition lex {T m A} {M:Monad m} {MF:MonadFix m} (token_ps:list (parser_t T m A)) : list T -> m (list A * list T) :=
  mfix $ fun lex input =>
    ls <- tmap (run_parser_t input) token_ps ;;
    match best_lex ls with
      | None => ret ([], input)
      | Some (o, input') =>
          rs <- lex input' ;;
          let '(os,ts) := rs in
          ret $ (o::os,ts)
    end.

(* ---------------------- *)

Definition xs : unit -> parser_t ascii (fuel_t option) (list ascii) :=
  mfix $ fun xs _ =>
    (fret cons <@> parse_token "x"%char <@> xs tt) <|> (fret nil).

Definition bad : unit -> parser_t ascii (fuel_t option) unit :=
  mfix $ fun bad _ =>
    parse_token "x"%char @> bad tt
    <|>
    parse_token "y"%char @> fret tt.

(*
Eval compute in (run_fuel_t 100 (un_parser_t (bad tt) (string2list "xyzx"))).
*)

Definition xx : unit -> parser_t ascii (fuel_t option) (ascii*ascii) :=
  mfix $ fun xs _ =>
    fret pair <@> parse_token "x"%char <@> parse_token "x"%char.

(*
Eval compute in (run_fuel_t 1000 (un_parser_t (xs tt) (string2list "x"))).
Eval compute in (run_fuel_t 1000 (un_parser_t (xx tt) (string2list "xx"))).
*)
