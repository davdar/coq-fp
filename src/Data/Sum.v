Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Categories.

Import CoreClassesNotation.
Import CoreDataNotation.

Section Injection.
  Context {A B} `{! Lte A ,! Eqv A ,! Lte B ,! Eqv B ,! PartialOrd A ,! PartialOrd B }.
  Global Instance sum_HI_inl : HasInjection A (A+B) := { inject := inl }.
  Global Instance sum_HI_inr : HasInjection B (A+B) := { inject := inr }.

  Global Instance sum_IR_inl_eq : InjectionRespect A (A+B) inl eq eq.
  Proof. constructor ; unfold Proper ; simpl in * ; intros ; congruence. Qed.
  Global Instance sum_IR_inr_eq : InjectionRespect B (A+B) inr eq eq.
  Proof. constructor ; unfold Proper ; simpl in * ; intros ; congruence. Qed.
End Injection.

Section EqDec.
  Context {A B} `{! EqDec A ,! EqDec B}.

  Definition sum_eq_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 =! a2
    | inr b1, inr b2 => b1 =! b2
    | _, _ => false
    end.

  Global Instance sum_EqDec : EqDec (A+B) := { eq_dec := sum_eq_dec }.

  Context `{! RelDecCorrect A eq eq_dec ,! RelDecCorrect B eq eq_dec }.

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
  Context {A B} `{! Eqv A ,! Eqv B}.

  Inductive sum_eqv : A+B -> A+B -> Prop :=
    | InlSumEqv : forall a1 a2 , a1 ~= a2 -> sum_eqv (inl a1) (inl a2)
    | InrSumEqv : forall b1 b2, b1 ~= b2 -> sum_eqv (inr b1) (inr b2).

  Global Instance sum_Eqv : Eqv (A+B) := { eqv := sum_eqv }.

  Section PER.
    Context `{! PER_WF A ,! PER_WF B}.
    Global Instance sum_PER_WF : PER_WF (A+B).
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
      unfold Symmetric ; intros.
        destruct x as [xl | xr], y as [yl | yr] ; repeat mysimp.
      unfold Transitive ; intros.
        destruct x as [xl | xr], y as [yl | yr], z as [zl | zr] ; repeat mysimp.
      Qed.
  End PER.

  Section ER.
    Context `{! ER_WF A ,! ER_WF B}.
    Global Instance sum_ER_WF : ER_WF (A+B).
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
  End ER.

  Global Instance sum_IR_inl_eqv : InjectionRespect A (A+B) inl eqv eqv.
  Proof.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
  Qed.

  Global Instance sum_IR_inr_eqv : InjectionRespect B (A+B) inr eqv eqv.
  Proof.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
  Qed.
End Eqv.

Section EqvDec.
  Context {A B} `{! EqvDec A ,! EqvDec B }.

  Definition sum_eqv_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 ~=! a2
    | inr b1, inr b2 => b1 ~=! b2
    | _, _ => false
    end.

  Global Instance sum_EqvDec : EqvDec (A+B) := { eqv_dec := sum_eqv_dec }.

  Context
    `{! Eqv A ,! RelDecCorrect A eqv eqv_dec
     ,! Eqv B ,! RelDecCorrect B eqv eqv_dec
     }.

  Global Instance sum_Eqv_RDC : RelDecCorrect (A+B) eqv eqv_dec.
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

Section PreOrd.
  Context {A B} `{! Lte A ,! Lte B }.

  Inductive sum_lte : A+B -> A+B -> Prop :=
    | InlSumLte : forall a1 a2, a1 <= a2 -> sum_lte (inl a1) (inl a2)
    | InrSumLte : forall b1 b2, b1 <= b2 -> sum_lte (inr b1) (inr b2)
    | LRSumLte : forall a1 b2, sum_lte (inl a1) (inr b2).
                      
  Global Instance sum_Lte : Lte (A+B) := { lte := sum_lte }.

  Global Instance sum_IR_inl_lte : InjectionRespect A (A+B) inl lte lte.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - constructor ; auto. 
    - inversion H ; auto.
  Qed.

  Global Instance sum_IR_inr_lte : InjectionRespect B (A+B) inr lte lte.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - constructor ; auto. 
    - inversion H ; auto.
  Qed.

  Context `{! PreOrd A ,! PreOrd B }.

  Section sum_PreOrd.
    Global Instance sum_PreOrd : PreOrd (A+B).
    Proof.
      Local Ltac mysimp :=
        match goal with
        | [ |- inl _ <= inl _ ] => constructor
        | [ |- inl _ <= inr _ ] => constructor
        | [ |- inr _ <= inr _ ] => constructor
        | [ H : inl _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ <= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ <= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H1 : ?x <= ?y , H2 : ?y <= ?z |- ?x <= ?z ] => transitivity y ; auto
        | _ => auto
        end.
      constructor.
      - unfold Reflexive ; intros.
        destruct x ; repeat mysimp ; reflexivity.
      - unfold Transitive ; intros.
        destruct x,y,z ; repeat mysimp.
    Qed.
  End sum_PreOrd.

  Context `{! LteDec A ,! LteDec B}.

  Definition sum_lte_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1,ab2 with
    | inl a1,inl a2 => a1 <=! a2
    | inl _,inr _ => true
    | inr _,inl _ => false
    | inr b1,inr b2 => b1 <=! b2
    end.
  Global Instance sum_LteDec : LteDec (A+B) := { lte_dec := sum_lte_dec }.

  Context `{! RelDecCorrect A lte lte_dec ,! RelDecCorrect B lte lte_dec }.

  Section sum_Lte_RDC.
    Global Instance sum_Lte_RDC : RelDecCorrect (A+B) lte lte_dec.
    Proof.
      Local Ltac mysimp :=
        match goal with
        | [ |- inl _ <= inl _ ] => constructor
        | [ |- inl _ <= inr _ ] => constructor
        | [ |- inr _ <= inr _ ] => constructor
        | [ |- _ <= _ ] => apply dec_correct
        | [ H : inl _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ <= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : _ <= _ |- _ ] => apply rel_correct in H
        | [ H : inr _ <=! inl _ = true |- _ ] => discriminate H
        | _ => auto
        end.
      constructor ; intros.
      - destruct x,y ; repeat mysimp.
      - destruct x,y ; repeat mysimp.
    Qed.
  End sum_Lte_RDC.
End PreOrd.

Section PartialOrd.
  Context {A B} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B }.

  Section sum_PartialOrd.
    Global Instance sum_PartialOrd : PartialOrd (A+B).
    Proof.
      Local Ltac mysimp :=
        match goal with
        | [ |- inl _ ~= inl _ ] => constructor
        | [ |- inr _ ~= inr _ ] => constructor
        | [ |- inl _ <= inl _ ] => constructor
        | [ |- inl _ <= inr _ ] => constructor
        | [ |- inr _ <= inr _ ] => constructor
        | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ <= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ <= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H1 : ?x <= ?y , H2 : ?y <= ?x |- ?x ~= ?y ] => apply antisymmetry ; auto
        | [ H1 : ?x <= _ , H2 : ?x0 ~= ?x |- ?x0 <= _ ] => rewrite H2
        | [ H1 : _ <= ?y , H2 : ?y0 ~= ?y |- _ <= ?y0 ] => rewrite H2
        | _ => auto
        end.
      constructor ; eauto with typeclass_instances.
      - constructor ; intros.
        destruct x,y ; repeat mysimp.
      - unfold Proper,"==>",impl,Basics.impl ; intros.
        destruct x,y,x0,y0 ; repeat mysimp.
        rewrite <- H3 ; rewrite <- H4 ; auto.
        rewrite <- H3 ; rewrite <- H4 ; auto.
    Qed.
  End sum_PartialOrd.

  Context `{! PartialOrdDec A ,! PartialOrdDec B }.

  Definition sum_pord_dec (ab1:A+B) (ab2:A+B) : option comparison :=
    match ab1,ab2 with
    | inl a1,inl a2 => a1 <~>! a2
    | inl _,inr _ => Some Lt
    | inr _,inl _ => Some Gt
    | inr b1,inr b2 => b1 <~>! b2
    end.

  Global Instance sum_PartialOrdDec : PartialOrdDec (A+B) := { pord_dec := sum_pord_dec }.

  Context `{! PartialOrdDecCorrect A ,! PartialOrdDecCorrect B }.

  Section sum_PartialOrdDecCorrect.
    Global Instance sum_PartialOrdDecCorrect : PartialOrdDecCorrect (A+B).
    Proof.
      Local Ltac mysimp :=
        match goal with
        | [ |- inl _ ~= inl _ ] => constructor
        | [ |- inr _ ~= inr _ ] => constructor
        | [ |- inl _ <= inr _ ] => constructor
        | [ |- inr _ <= inr _ ] => constructor
        | [ |- inl _ < inl _ ] => apply InjectionRespect_eta
        | [ |- inl _ < inr _ ] => constructor
        | [ |- inr _ < inr _ ] => apply InjectionRespect_eta
        | [ |- inl _ >< inl _ ] => apply InjectionRespect_eta
        | [ |- inr _ >< inr _ ] => apply InjectionRespect_eta
        | [ |- _ <~>! _ = Some Eq ] => apply pord_rel_correct_eqv
        | [ |- _ <~>! _ = Some Lt ] => apply pord_rel_correct_lt
        | [ |- _ <~>! _ = Some Gt ] => apply pord_rel_correct_gt
        | [ |- _ <~>! _ = None ] => apply pord_rel_correct_un
        | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : ~ inl _ <= inr _ |- _ ] => exfalso ; apply H
        | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ < inl _ |- _ ] => apply InjectionRespect_beta in H
        | [ H : inr _ < inr _ |- _ ] => apply InjectionRespect_beta in H
        | [ H : inr _ < inl _ |- _ ] => destruct H
        | [ H : inl _ >< inl _ |- _ ] => apply InjectionRespect_beta in H
        | [ H : inl _ >< inr _ |- _ ] => destruct H
        | [ H : inr _ >< inl _ |- _ ] => destruct H
        | [ H : inr _ >< inr _ |- _ ] => destruct H
        | [ H : inl _ <~>! inr _ = Some Eq |- _ ] => discriminate H
        | [ H : _ <~>! _ = Some Eq |- _ ] => apply pord_dec_correct_eqv in H
        | [ H : _ <~>! _ = Some Lt |- _ ] => apply pord_dec_correct_lt in H
        | [ H : _ <~>! _ = Some Gt |- _ ] => apply pord_dec_correct_gt in H
        | [ H : _ <~>! _ = None |- _ ] => apply pord_dec_correct_un in H
        | [ H1 : ~ inr ?x <= inr ?y , H2 : ~ inr ?y <= inr ?x |- ?x >< ?y ] =>
            constructor ; unfold "~" ; intros ; [ apply H1 | apply H2]
        | [ |- ~ inr _ <= inl _ ] => unfold "~" ; intros
        | _ => auto
        end.
      constructor ; intros ; destruct x,y ; simpl in * ; repeat mysimp ; try congruence.
    Qed.
  End sum_PartialOrdDecCorrect.
End PartialOrd.

Section TotalOrd.
  Context {A B} `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B }.

  Section sum_TotalOrd.
    Global Instance sum_TotalOrd : TotalOrd (A+B).
    Proof.
      Local Ltac mysimp :=
        match goal with
        | [ |- inl _ <= inl _ ] => constructor
        | [ |- inl _ <= inr _ ] => constructor
        | [ |- inr _ <= inr _ ] => constructor
        | _ => auto
        end.
      constructor ; eauto with typeclass_instances ; intros.
      unfold "~" at 1 ; intros H ; destruct H.
      destruct x,y.
      - apply (TotalOrd_comparable (x:=a) (y:=a0))
        ; constructor ; unfold "~" ; intros ; [ apply H | apply H0 ]
        ; repeat mysimp.
      - apply H ; repeat mysimp.
      - apply H0 ; repeat mysimp.
      - apply (TotalOrd_comparable (x:=b) (y:=b0))
        ; constructor ; unfold "~" ; intros ; [ apply H | apply H0 ]
        ; repeat mysimp.
    Qed.
  End sum_TotalOrd.

  Context `{! TotalOrdDec A ,! TotalOrdDec B }.

  Definition sum_tord_dec (ab1:A+B) (ab2:A+B) : comparison :=
    match ab1,ab2 with
    | inl a1,inl a2 => a1 <=>! a2
    | inl _,inr _ => Lt
    | inr _,inl _ => Gt
    | inr b1,inr b2 => b1 <=>! b2
    end.

  Global Instance sum_TotalOrdDec : TotalOrdDec (A+B) := { tord_dec := sum_tord_dec }.

  Context `{! TotalOrdDecCorrect A ,! TotalOrdDecCorrect B }.

  Section sum_TotalOrdDecCorrect.
    Global Instance sum_TotalOrdDecCorrect : TotalOrdDecCorrect (A+B).
    Proof.
      Local Ltac mysimp :=
        match goal with
        | [ |- inl _ ~= inl _ ] => constructor
        | [ |- inr _ ~= inr _ ] => constructor
        | [ |- inl _ <= inr _ ] => constructor
        | [ |- inl _ < inl _ ] => apply InjectionRespect_eta
        | [ |- inl _ < inr _ ] => constructor
        | [ |- inr _ < inr _ ] => apply InjectionRespect_eta
        | [ |- _ <=>! _ = Eq ] => apply tord_rel_correct_eqv
        | [ |- _ <=>! _ = Lt ] => apply tord_rel_correct_lt
        | [ |- _ <=>! _ = Gt ] => apply tord_rel_correct_gt
        | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
        | [ H : inl _ < inl _ |- _ ] => apply InjectionRespect_beta in H
        | [ H : inr _ < inr _ |- _ ] => apply InjectionRespect_beta in H
        | [ H : inr _ < inl _ |- _ ] => destruct H
        | [ H : _ <=>! _ = Eq |- _ ] => apply tord_dec_correct_eqv in H
        | [ H : _ <=>! _ = Lt |- _ ] => apply tord_dec_correct_lt in H
        | [ H : _ <=>! _ = Gt |- _ ] => apply tord_dec_correct_gt in H
        | [ |- ~ inr _ <= inl _ ] => unfold "~" ; intros
        | _ => auto
        end.
      constructor ; intros ; destruct x,y ; simpl in * ; repeat mysimp ; try congruence.
    Qed.
  End sum_TotalOrdDecCorrect.
End TotalOrd.

Section Lattice.
  Context {A B} `{! Lattice A ,! Lattice B }.

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

  Context
    `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! LatticeWF A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! LatticeWF B
     }.

  Section sum_LatticeWF.
    Global Instance sum_LatticeWF : LatticeWF (A+B).
    Proof.
      Local Ltac mysimp :=
        match goal with
        | [ |- and _ _ ] => constructor
        | [ |- inl _ <= inl _ ] => eapply InjectionRespect_eta
        | [ |- inl _ <= inr _ ] => constructor
        | [ |- inr _ <= inr _ ] => eapply InjectionRespect_eta
        | [ |- (?a /\ _) <= ?a ] => apply lmeet_ineq
        | [ |- (_ /\ ?a) <= ?a ] => apply lmeet_ineq
        | [ |- ?a <= (?a \/ _) ] => apply ljoin_ineq
        | [ |- ?a <= (_ \/ ?a) ] => apply ljoin_ineq
        | [ |- ?a <= ?a ] => reflexivity
        | _ => auto
        end.
      constructor ; intros ; destruct t1,t2 ; unfold "/\","\/" ; simpl ; repeat mysimp.
    Qed.
  End sum_LatticeWF.

  Context `{! BoundedLattice A ,! BoundedLattice B }.

  Definition sum_top : A+B := inr ltop.
  Definition sum_bot : A+B := inl lbot.

  Global Instance sum_BoundedLattice : BoundedLattice (A+B) :=
    { ltop := sum_top
    ; lbot := sum_bot
    }.

  Context `{! BoundedLatticeWF A ,! BoundedLatticeWF B }.

  Global Instance sum_BoundedLatticeWF : BoundedLatticeWF (A+B).
    constructor ; eauto with typeclass_instances ; intros.
    - destruct t ; constructor.
      apply ltop_ineq.
    - destruct t ; constructor.
      apply lbot_ineq.
  Qed.
End Lattice.

(*
Section sum_t_Monad.
  Context {A:Type} {m} {M:Monad m}.

  Definition run_sum_t {B} : sum_t A m B -> m (A+B) := un_sum_t.

  Section Monad.
    Definition sum_t_funit {B} : B -> sum_t A m B := SumT '.' ret '.' inr.
    Global Instance sum_t_FUnit : FUnit (sum_t A m) :=
      { funit := @sum_t_funit }.

    Definition sum_t_bind {B C} (bMM:sum_t A m B) (f:B -> sum_t A m C) : sum_t A m C :=
      SumT $ begin
        ab <- un_sum_t bMM ;;
        match ab with
        | inl x => ret $ inl x
        | inr y => un_sum_t $ f y
        end
      end.
    Global Instance sum_t_Monad : MBind (sum_t A m) :=
      { bind := @sum_t_bind }.
  End Monad.

  Section MonadError.
    Definition sum_t_throw {B} : A -> sum_t A m B := SumT '.' ret '.' inl.
    Definition sum_t_catch {B}
        (bMM:sum_t A m B) (h:A -> sum_t A m B) : sum_t A m B :=
      SumT $ begin
        ab <-  un_sum_t bMM ;;
        match ab with
        | inl x => un_sum_t $ h x
        | inr y => ret $ inr y
        end
      end.
    Global Instance sum_t_MonadError : MError A (sum_t A m) :=
      { throw := @sum_t_throw
      ; catch := @sum_t_catch
      }.
  End MonadError.

  Section MonadPlus.
    Context {AM:Monoid A}.

    Definition sum_t_mzero {B} : sum_t A m B := SumT $ ret $ inl gunit.
    Definition sum_t_mplus {B C} (bMM:sum_t A m B) (cMM:sum_t A m C)
        : sum_t A m (B+C) :=
      SumT $ begin
        ab <- un_sum_t bMM ;;
        match ab with
        | inl e1 =>
            ac <- un_sum_t cMM ;;
            match ac with
            | inl e2 => ret $ inl $ e1 ** e2
            | inr c => ret $ inr $ inr c
            end
        | inr b => ret $ inr $ inl b
        end
      end.
    (*
    Global Instance sum_t_MonadPlus : MonadPlus (sum_t A m) :=
      { mzero := @sum_t_mzero
      ; mplus := @sum_t_mplus
      }.
*)
  End MonadPlus.

  Section MonadFix.
    Context {MF:MFix m}.

    Definition sum_t_mfix {B C}
        (ff:(B -> sum_t A m C) -> B -> sum_t A m C) (b:B) : sum_t A m C :=
      let ff' (f':B -> m (A+C)) :=
        let f := SumT '.' f' in
        un_sum_t '.' ff f
      in
      SumT $ mfix ff' b.
    Global Instance sum_t_MonadFix : MFix (sum_t A m) :=
      { mfix := @sum_t_mfix }.
  End MonadFix.
End sum_t_Monad.

Instance sum_sum_t_FunctorInjection {A} : HasFunctorInjection (sum A) (sum_t A identity) :=
  { finject := fun _ => SumT '.' Identity }.
Instance sum_t_sum_FunctorInjection {A} : HasFunctorInjection (sum_t A identity) (sum A) :=
  { finject := fun _ => run_identity '.' run_sum_t }.

Instance sum_FUnit {A} : FUnit (sum A) := Deriving_FUnit (sum_t A identity).
Instance sum_MBind {A} : MBind (sum A) := Deriving_MBind (sum_t A identity).
(*
Instance sum_MonadPlus {A} {AM:Monoid A} : MonadPlus (sum A) :=
  iso_MonadPlus (sum_t A identity).
Instance sum_MonadError {A} : MonadError A (sum A) :=
  iso_MonadError (sum_t A identity).
*)

*)