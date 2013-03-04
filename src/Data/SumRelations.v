Require Import FP.Data.Ascii.
Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Data.String.
Require Import FP.Data.Sum.
Require Import FP.Relations.RelDec.
Require Import FP.Relations.Setoid.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Show.

Import CharNotation.
Import EqDecNotation.
Import EqvNotation.
Import FunctionNotation.
Import LatticeNotation.
Import OrdNotation.
Import MonoidNotation.
Import StringNotation.
Import ProperNotation.

Section EqDec.
  Context {A B} {AED:EqDec A} {BED:EqDec B}.

  Definition sum_eq_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 =! a2
    | inr b1, inr b2 => b1 =! b2
    | _, _ => false
    end.

  Global Instance sum_EqDec : EqDec (A+B) := { eq_dec := sum_eq_dec }.

  Context {ARDC:RelDecCorrect A eq eq_dec}.
  Context {BRDC:RelDecCorrect B eq eq_dec}.

  Global Instance sum_Eq_RelDecCorrect : RelDecCorrect (A+B) eq eq_dec.
  Proof. constructor ; intros ;
    destruct x as [xl | xr], y as [yl | yr] ; intros ;
      simpl in * ; repeat
        match goal with
        | [ H : _ =! _ = true |- _ ] => apply dec_correct in H
        | [ |- _ =! _ = true ] => apply rel_correct
        | _ => auto
        end ; try congruence.
    Qed.
End EqDec.

Section Eqv.
  Context {A B} {AE:Eqv A} {BE:Eqv B}.

  Inductive sum_eqv : A+B -> A+B -> Prop :=
    | InlSumEqv : forall a1 a2 , a1 ~= a2 -> sum_eqv (inl a1) (inl a2)
    | InrSumEqv : forall b1 b2, b1 ~= b2 -> sum_eqv (inr b1) (inr b2).

  Global Instance sum_Eqv : Eqv (A+B) := { eqv := sum_eqv }.

  Context {AEE:EqvWF A} {BEE:EqvWF B}.

  Global Instance sum_EqvWF : EqvWF (A+B).
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ ~= inl _ ] => constructor
      | [ |- inr _ ~= inr _ ] => constructor
      | [ |- ?x ~= ?x ] => reflexivity

      | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inr _ |- _ ] => inversion H
      | [ H : inr _ ~= inl _ |- _ ] => inversion H
      | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H

      | [ H : ?x ~= ?y |- ?y ~= ?x ] => symmetry ; exact H
      | [ H1 : ?x ~= ?y, H2 : ?y ~= ?z |- ?x ~= ?z ] =>
          transitivity y ; [exact H1 | exact H2]
      | _ => auto
      end.
    constructor ; constructor ; intros.
    unfold Reflexive ; intros.
      destruct x ; repeat mysimp.
    unfold Symmetric ; intros.
      destruct x as [xl | xr], y as [yl | yr] ; repeat mysimp.
    unfold Transitive ; intros.
      destruct x as [xl | xr], y as [yl | yr], z as [zl | zr] ; repeat mysimp.
    Qed.

  Global Instance sum_InjectionRespect_eqv_inl : InjectionRespect A (A+B) inl eqv eqv.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
    Qed.

  Global Instance sum_InjectionRespect_eqv_inr : InjectionRespect B (A+B) inr eqv eqv.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
    Qed.
End Eqv.

Section EqvDec.
  Context {A B} {AED:EqvDec A} {BED:EqvDec B}.

  Definition sum_eqv_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 ~=! a2
    | inr b1, inr b2 => b1 ~=! b2
    | _, _ => false
    end.

  Global Instance sum_EqvDec : EqvDec (A+B) := { eqv_dec := sum_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect A eqv eqv_dec}.
  Context {BE:Eqv B} {BRDC:RelDecCorrect B eqv eqv_dec}.

  Global Instance sum_Eqv_RelDecCorrect : RelDecCorrect (A+B) eqv eqv_dec.
  Proof. constructor ; intros ;
    destruct x as [xl | xr], y as [yl | yr] ; intros ;
      simpl in * ; repeat 
        match goal with
        | [ H : inl _ ~=! _ = _ |- _ ] => unfold "~=!" in H ; simpl in H
        | [ H : inr _ ~=! _ = _ |- _ ] => unfold "~=!" in H ; simpl in H
        | [ |- inl _ ~=! _ = _ ] => unfold "~=!" ; simpl
        | [ |- inr _ ~=! _ = _ ] => unfold "~=!" ; simpl
        | [ |- _ ~=! _ = true ] => apply rel_correct
        | [ |- _ ~= _ ] => constructor
        | [ H : _ ~=! _ = true |- _ ] => apply dec_correct in H
        | [ H : _ ~= _ |- _ ] => inversion H ; clear H
        | _ => auto
        end ; try congruence.
    Qed.
End EqvDec.

Section Ord.
  Context {A B} {AL:Ord A} {BL:Ord B}.

  Inductive sum_lt : A+B -> A+B -> Prop :=
    | InlSumLte : forall a1 a2, a1 < a2 -> sum_lt (inl a1) (inl a2)
    | InrSumLte : forall b1 b2, b1 < b2 -> sum_lt (inr b1) (inr b2)
    | MisSumLte : forall a1 b2, sum_lt (inl a1) (inr b2).
      
  Global Instance sum_Ord : Ord (A+B) := { lt := sum_lt }.

  Context {EA:Eqv A} {EAWF:EqvWF A} {ALWF:OrdWF A}.
  Context {EB:Eqv B} {EBWF:EqvWF B} {BLWF:OrdWF B}.

  Global Instance sum_OrdWF : OrdWF (A+B).
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ < inl _ ] => constructor
      | [ |- inl _ < inr _ ] => constructor
      | [ |- inr _ < inr _ ] => constructor
      | [ H : inl _ < inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ < inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ < inl _ |- _ ] => inversion H
      | [ H : inr _ < inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inr _ |- _ ] => inversion H
      | [ H : inr _ ~= inl _ |- _ ] => inversion H
      | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : ?a < ?a |- False ] => apply (irreflexivity H)
      | [ H1 : ?a < ?b, H2 : ?b < ?c |- ?a < ?c ] =>
          transitivity b ; [exact H1 | exact H2]
      | [ H1 : ?a ~= ?a', H2 : ?b ~= ?b', H3 : ?a < ?b |- ?a' < ?b' ] =>
          eapply (lt_resp_eqv _ _ H1 _ _ H2) ; auto
      | [ H1 : ?a' ~= ?a, H2 : ?b' ~= ?b, H3 : ?a < ?b |- ?a' < ?b' ] =>
          eapply (lt_resp_eqv _ _ H1 _ _ H2) ; auto
      | _ => auto
      end.
    constructor.
    unfold Irreflexive, Reflexive, complement ; intros.
      destruct x; repeat mysimp.
    unfold Transitive ; intros.
      destruct x, y, z ; repeat mysimp.
    unfold Proper ; simpl ; intros t1 t2 e1 t3 t4 e2 ineq ;
      destruct t1, t2, t3, t4 ; repeat mysimp.
    Qed.

  Global Instance sum_InjectionRespect_lt_inl : InjectionRespect A (A+B) inl lt lt.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
    Qed.
  Global Instance sum_InjectionRespect_lt_inr : InjectionRespect B (A+B) inr lt lt.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
    Qed.
End Ord.

Section OrdDec.
  Context {A B:Type}.

  Definition sum_ord_dec_b
      (a_ord_dec:A -> A -> comparison) (b_ord_dec:B -> B -> comparison)
      (ab1:A+B) (ab2:A+B) : comparison :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 `a_ord_dec` a2
    | inr b1, inr b2 => b1 `b_ord_dec` b2
    | inl _, inr _ => Lt
    | inr _, inl _ => Gt
    end.

  Context {ALD:OrdDec A} {BLD:OrdDec B}.

  Definition sum_ord_dec : A+B -> A+B -> comparison := sum_ord_dec_b ord_dec ord_dec.

  Global Instance sum_OrdDec : OrdDec (A+B) := { ord_dec := sum_ord_dec }.

  Context {AE:Eqv A} {AO:Ord A} {BE:Eqv B} {BO:Ord B}.
  Context {ARDC:OrdDecCorrect A}.
  Context {BRDC:OrdDecCorrect B}.

  Global Instance sum_OrdDecCorrect : OrdDecCorrect (A+B).
  Proof. constructor ; intros x y ; destruct x, y ; intros ; simpl in * ;
      repeat
        match goal with
        | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ ~= inr _ |- _ ] => inversion H
        | [ H : inr _ ~= inl _ |- _ ] => inversion H
        | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ |- inl _ ~= inl _ ] => constructor
        | [ |- inr _ ~= inr _ ] => constructor
        | [ H : inl _ < inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ < inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ < inl _ |- _ ] => inversion H
        | [ H : inr _ < inr _ |- _ ] => inversion H ; subst ; clear H
        | [ |- inl _ < inl _ ] => constructor
        | [ |- inl _ < inr _ ] => constructor
        | [ |- inr _ < inr _ ] => constructor
        | [ H : _ <=>! _ = Eq |- _ ] => apply ord_dec_correct_eqv in H
        | [ H : _ <=>! _ = Lt |- _ ] => apply ord_dec_correct_lt in H
        | [ H : _ <=>! _ = Gt |- _ ] => apply ord_dec_correct_gt in H
        | [ |- _ <=>! _ = Eq ] => apply ord_rel_correct_eqv
        | [ |- _ <=>! _ = Lt ] => apply ord_rel_correct_lt
        | [ |- _ <=>! _ = Gt ] => apply ord_rel_correct_gt
        | _ => auto
        end ; try congruence.
   Qed.
End OrdDec.

Section Lattice.
  Context {A B:Type}.
  Context {AL:Lattice A} {BL:Lattice B}.

  Definition sum_meet (s1:A+B) (s2:A+B) : A+B :=
    match s1, s2 with
    | inl a1, inl a2 => inl $ a1 /\ a2
    | inl a1, inr _ => inl a1
    | inr _, inl a2 => inl a2
    | inr b1, inr b2 => inr $ b1 /\ b2
    end.
  Definition sum_join (s1:A+B) (s2:A+B) : A+B :=
    match s1,s2 with
    | inl a1, inl a2 => inl $ a1 \/ a2
    | inl _, inr b2 => inr b2
    | inr b1, inl _ => inr b1
    | inr b1, inr b2 => inr $ b1 \/ b2
    end.

  Global Instance sum_Lattice : Lattice (A+B) :=
    { lmeet := sum_meet
    ; ljoin := sum_join
    }.

  Context {EA:Eqv A} {AO:Ord A} {EB:Eqv B} {BO:Ord B}.
  Context {EAWF:EqvWF A} {OAWF:OrdWF A}.
  Context {EBWF:EqvWF B} {OBWF:OrdWF B}.
  Context {ALWF:LatticeWF A} {BLWF:LatticeWF B}.

  Lemma inlr_lte : forall (a:A) (b:B), inl a <= inr b.
    left ; constructor. Qed.

  Global Instance sum_LatticeWF : LatticeWF (A+B).
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ <= inl _ ] => eapply InjectionRespect_eta
      | [ |- inl _ <= inr _ ] => apply inlr_lte
      | [ |- inr _ <= inr _ ] => eapply InjectionRespect_eta
      | [ |- (?a /\ _) <= ?a ] => apply lmeet_ineq
      | [ |- (_ /\ ?a) <= ?a ] => apply lmeet_ineq
      | [ |- ?a <= (?a \/ _) ] => apply ljoin_ineq
      | [ |- ?a <= (_ \/ ?a) ] => apply ljoin_ineq
      | [ |- ?a <= ?a ] => reflexivity
      | _ => auto
      end.
    constructor ; intros ; unfold lmeet, ljoin in * ; simpl in *.
    destruct t1, t2 ; constructor ; simpl ; repeat mysimp.
    destruct t1, t2 ; constructor ; simpl ; repeat mysimp.
    Qed.

  Context {ABL:BoundedLattice A} {BBL:BoundedLattice B}.

  Definition sum_top : A+B := inr ltop.
  Definition sum_bot : A+B := inl lbot.

  Global Instance sum_BoundedLattice : BoundedLattice (A+B) :=
    { ltop := sum_top
    ; lbot := sum_bot
    }.

  Context {ABLWF:BoundedLatticeWF A} {BBLWF:BoundedLatticeWF B}.

  Global Instance sum_BoundedLatticeWF : BoundedLatticeWF (A+B).
    constructor ; eauto with typeclass_instances ; intros.
      destruct t.
        left ; constructor.
        destruct (ltop_ineq b).
          left ; constructor ; auto.
          right ; constructor ; auto.
      destruct t.
        destruct (lbot_ineq a).
          left ; constructor ; auto.
          right ; constructor ; auto.
        left ; constructor.
    Qed.
End Lattice.

Section Injection.
  Context {A B:Type} {AE:Eqv A} {BE:Eqv B} {AO:Ord A} {BO:Ord B}.
  Global Instance sum_HasInjection_inl : HasInjection A (A+B) :=
    { inject := inl }.
  Global Instance sum_HasInjection_inr : HasInjection B (A+B) :=
    { inject := inr }.

  Global Instance sum_InjectionRespect_inl_eq : InjectionRespect A (A+B) inl eq eq.
    constructor ; unfold Proper ; simpl in * ; intros ; congruence. Qed.
  Global Instance sum_InjectionRespect_inr_eq : InjectionRespect B (A+B) inr eq eq.
    constructor ; unfold Proper ; simpl in * ; intros ; congruence. Qed.

  Global Instance sum_inl_InjectionRespect_eqv : InjectionRespect A (A+B) inl eqv eqv.
  Proof.
    constructor ; unfold Proper ; simpl ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
  Qed.
  Global Instance sum_inr_InjectionRespect_eqv : InjectionRespect B (A+B) inr eqv eqv.
  Proof.
    constructor ; unfold Proper ; simpl ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
  Qed.

  Global Instance sum_inl_InjectionRespect_lt : InjectionRespect A (A+B) inl lt lt.
  Proof.
    constructor ; unfold Proper ; simpl ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
  Qed.
  Global Instance sum_inr_InjectionRespect_lt : InjectionRespect B (A+B) inr lt lt.
  Proof.
    constructor ; unfold Proper ; simpl ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
  Qed.
End Injection.

Section Show.
  Context {A B} {AS:Show A} {BS:Show B}.

  Section sum_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition sum_show (ab:A+B) : R :=
      let (tag, payload) :=
        match ab with
        | inl a => ("inl", show a)
        | inr b => ("inr", show b)
        end
      in raw_char "("%char
      ** raw_string tag
      ** raw_char " "%char
      ** payload
      ** raw_char ")"%char.
  End sum_show.

  Global Instance sum_Show : Show (A+B) := { show := sum_show }.
End Show.