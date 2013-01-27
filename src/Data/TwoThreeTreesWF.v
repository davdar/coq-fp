Require Import FP.Data.TwoThreeTrees.
Require Import FP.Structures.WellFormed.
Require Import FP.Data.N.
Require Import FP.Data.Unit.
Require Import FP.Data.Sum.
Require Import FP.Data.Ext.
Require Import FP.Structures.Peano.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Additive.
Require Import FP.Relations.RelDec.

Import OrdNotation.
Import AdditiveNotation.

Module TwoThreeTreesWF.
  Import TwoThreeTrees.

  Section Context.
    Context {K:Type}.
    Context {E:Eqv K}.
    Context {O:Ord K} {OWF:OrdWF K}.
    Context {L:Lattice K} {B:BoundedLattice K}.
    Context {OD:OrdDec K} {ODC:OrdDecCorrect K}.
    Context {V:Type}.

    Inductive tree_iwf : ext_top_bot K -> ext_top_bot K -> N -> tree K V -> Prop :=
      | NullWF :
          forall
            t_lower_bound t_upper_bound,
              tree_iwf t_lower_bound t_upper_bound 0 Null_t
      | TwoWF :
          forall
            tl tl_lower_bound tl_upper_bound
            tr tr_lower_bound tr_upper_bound
            t_height
            km vm,
              tree_iwf tl_lower_bound tl_upper_bound t_height tl
           -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
           -> tl_upper_bound < inject km < tr_lower_bound
           -> tree_iwf tl_lower_bound tr_upper_bound (t_height+1)
                       (Two_t tl (km,vm) tr)
      | ThreeWF :
          forall
            tl tl_lower_bound tl_upper_bound
            tm tm_lower_bound tm_upper_bound
            tr tr_lower_bound tr_upper_bound
            t_height
            kl vl kr vr,
              tree_iwf tl_lower_bound tl_upper_bound t_height tl
           -> tree_iwf tm_lower_bound tm_upper_bound t_height tm
           -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
           -> tl_upper_bound < inject kl < tm_lower_bound
           -> tm_upper_bound < inject kr < tr_lower_bound
           -> tree_iwf tl_lower_bound tr_upper_bound (t_height+1)
                       (Three_t tl (kl,vl) tm (kr,vr) tr).

    Inductive context_iwf
        : ext_top_bot K -> ext_top_bot K -> N (* bounds and height of hole *)
       -> ext_top_bot K -> ext_top_bot K -> N (* bounds and height when filled *)
       -> context K V
       -> Prop :=
      | TopWF :
          forall
            t_lower_bound t_upper_bound
            t_height,
              context_iwf t_lower_bound t_upper_bound t_height
                          t_lower_bound t_upper_bound t_height Top_c
      | TwoLeftHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tr tr_lower_bound tr_upper_bound
            c c_lower_bound c_upper_bound c_height
            k v,
              context_iwf h_lower_bound tr_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tr_lower_bound tr_upper_bound h_height tr
           -> h_upper_bound < inject k < tr_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (TwoLeftHole_c (k,v) tr c)
      | TwoRightHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tl tl_lower_bound tl_upper_bound
            c c_lower_bound c_upper_bound c_height
            k v,
              context_iwf tl_lower_bound h_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tl_lower_bound tl_upper_bound h_height tl
           -> tl_upper_bound < inject k < h_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (TwoRightHole_c tl (k,v) c)
      | ThreeLeftHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tm tm_lower_bound tm_upper_bound
            tr tr_lower_bound tr_upper_bound
            c c_lower_bound c_upper_bound c_height
            kl vl kr vr,
              context_iwf h_lower_bound tr_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tm_lower_bound tm_upper_bound h_height tm
           -> tree_iwf tr_lower_bound tr_upper_bound h_height tr
           -> h_upper_bound < inject kl < tm_lower_bound
           -> tm_upper_bound < inject kr < tr_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (ThreeLeftHole_c (kl,vl) tm (kr,vr) tr c)
      | ThreeMiddleHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tl tl_lower_bound tl_upper_bound
            tr tr_lower_bound tr_upper_bound
            c c_lower_bound c_upper_bound c_height
            kl vl kr vr,
              context_iwf tl_lower_bound tr_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tl_lower_bound tl_upper_bound h_height tl
           -> tree_iwf tr_lower_bound tr_upper_bound h_height tr
           -> tl_upper_bound < inject kl < h_lower_bound
           -> h_upper_bound < inject kr < tr_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (ThreeMiddleHole_c tl (kl,vl) (kr,vr) tr c)
      | ThreeRightHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tl tl_lower_bound tl_upper_bound
            tm tm_lower_bound tm_upper_bound
            c c_lower_bound c_upper_bound c_height
            kl vl kr vr,
              context_iwf tl_lower_bound h_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tl_lower_bound tl_upper_bound h_height tl
           -> tree_iwf tm_lower_bound tm_upper_bound h_height tm
           -> tl_upper_bound < inject kl < tm_lower_bound
           -> tm_upper_bound < inject kr < h_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (ThreeRightHole_c tl (kl,vl) tm (kr,vr) c).

  Inductive location_iwf 
      : ext_top_bot K -> ext_top_bot K -> N (* bounds and height of hole *)
     -> ext_top_bot K -> ext_top_bot K -> N (* bounds and height when filled *)
     -> location K V
     -> Prop :=
    | TwoHoleWF :
        forall
          t_height
          tl tl_lower_bound tl_upper_bound
          tr tr_lower_bound tr_upper_bound
          c c_lower_bound c_upper_bound c_height,
            tree_iwf tl_lower_bound tl_upper_bound t_height tl
         -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
         -> context_iwf tl_lower_bound tr_upper_bound (t_height+1)
                        c_lower_bound c_upper_bound c_height c
         -> location_iwf tl_upper_bound tr_lower_bound t_height
                         c_lower_bound c_upper_bound c_height
                         (TwoHole_l tl tr c).
            
  Global Instance tree_WellFormed : WellFormed (tree K V) :=
    { wf :=
        fun (t:tree K V) =>
          exists (n:N) (lb:ext_top_bot K) (ub:ext_top_bot K),
            tree_iwf lb ub n t
    }.

  Local Ltac mysimp :=
  match goal with
   | [ |- tree_iwf _ _ _ (Two_t _ _ _) ] => econstructor
   | [ |- tree_iwf _ _ _ (Three_t _ _ _ _ _) ] => econstructor
   | [ |- context_iwf _ _ _ _ _ _ Top_c ] => econstructor
   | [ |- context_iwf _ _ _ _ _ _ (TwoLeftHole_c _ _ _) ] => econstructor
   | [ |- context_iwf _ _ _ _ _ _ (TwoRightHole_c _ _ _) ] => econstructor
   | [ |- context_iwf _ _ _ _ _ _ (ThreeLeftHole_c _ _ _ _ _) ] => econstructor
   | [ |- context_iwf _ _ _ _ _ _ (ThreeMiddleHole_c _ _ _ _ _) ] => econstructor
   | [ |- context_iwf _ _ _ _ _ _ (ThreeRightHole_c _ _ _ _ _) ] => econstructor
   | [ H : tree_iwf _ _ _ Null_t |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : tree_iwf _ _ _ (Two_t _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : tree_iwf _ _ _ (Three_t _ _ _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : context_iwf _ _ _ _ _ _ Top_c |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : context_iwf _ _ _ _ _ _ (TwoLeftHole_c _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : context_iwf _ _ _ _ _ _ (TwoRightHole_c _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : context_iwf _ _ _ _ _ _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : context_iwf _ _ _ _ _ _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : context_iwf _ _ _ _ _ _ (ThreeRightHole_c _ _ _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : location_iwf _ _ _ _ _ _ (TwoHole_l _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : location_iwf _ _ _ _ _ _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | [ H : location_iwf _ _ _ _ _ _ (ThreeRightHole_l _ _ _ _ _) |- _ ] =>
       inversion H ; subst ; clear H
   | _ => eauto
  end.

  Lemma zip_wf :
    forall 
      (c:context K V) (t:tree K V)
      t_lower_bound t_upper_bound t_height
      c_lower_bound c_upper_bound c_height,
        tree_iwf t_lower_bound t_upper_bound t_height t
     -> context_iwf t_lower_bound t_upper_bound t_height
                    c_lower_bound c_upper_bound c_height c
     -> tree_iwf c_lower_bound c_upper_bound c_height (zip t c).
  Proof.
    intros c.
    induction c ; simpl ; intros ; repeat mysimp ; eapply IHc ; repeat mysimp.
  Qed.
  Hint Resolve zip_wf.

  Lemma fuse_wf :
    forall
      (c1:context K V) (c2:context K V)
      c1h_lower_bound c1h_upper_bound c1h_height
      c1_lower_bound c1_upper_bound c1_height
      c2_lower_bound c2_upper_bound c2_height,
        context_iwf c1h_lower_bound c1h_upper_bound c1h_height
                    c1_lower_bound c1_upper_bound c1_height c1
     -> context_iwf c1_lower_bound c1_upper_bound c1_height
                    c2_lower_bound c2_upper_bound c2_height c2
     -> context_iwf c1h_lower_bound c1h_upper_bound c1h_height
                    c2_lower_bound c2_upper_bound c2_height (fuse c1 c2).
  Proof.
    intros c1.
    induction c1 ; simpl ; intros ; repeat mysimp.
  Qed.
  Hint Resolve fuse_wf.

  Lemma fill_location_wf :
    forall
      (l:location K V) (k:K) (v:V)
      h_lower_bound h_upper_bound h_height
      c_lower_bound c_upper_bound c_height,
        h_lower_bound < inject k < h_upper_bound
     -> location_iwf h_lower_bound h_upper_bound h_height
                     c_lower_bound c_upper_bound c_height l
     -> tree_iwf c_lower_bound c_upper_bound c_height (fill_location (k,v) l).
  Proof.
    intros l.
    induction l ; intros ; repeat mysimp.
    eapply zip_wf ; repeat mysimp.
  Qed.
  Hint Resolve fill_location_wf.

  Lemma locate_wf :
    forall
      (t:tree K V) (k:K) (c:context K V)
      t_lower_bound t_upper_bound t_height
      c_lower_bound c_upper_bound c_height,
        t_lower_bound < inject k < t_upper_bound
     -> tree_iwf t_lower_bound t_upper_bound t_height t
     -> context_iwf t_lower_bound t_upper_bound t_height
                    c_lower_bound c_upper_bound c_height c
     -> exists h_lower_bound h_upper_bound,
          h_lower_bound < inject k < h_upper_bound
       /\ match locate k t c with
          | inl c =>
              context_iwf h_lower_bound h_upper_bound 0
                          c_lower_bound c_upper_bound c_height c
          | inr ((k,v),l) =>
              exists h_height,
                location_iwf h_lower_bound h_upper_bound h_height
                             c_lower_bound c_upper_bound c_height l
          end.
  Proof.
    intros t.
    induction t ; intros ; simpl ; repeat mysimp.
    simpl.
    remember (k <=>! km) as cmp ; destruct cmp.

    symmetry in Heqcmp.
    eapply ord_dec_correct_eqv in Heqcmp.
    rewrite Heqcmp in H.
    rewrite H0 in * ; clear H0 ; clear Heqcmp.

    exists tl_upper_bound.
    exists tr_lower_bound.
    split.
    auto.
    exists t_height0.
    econstructor.
    eapply H8.
    eapply H9.
    eapply H1.

    assert (lt k km). admit.
    assert (t_lower_bound < inject km < tr_lower_bound).
      split.
      transitivity (inject k).

    eapply IHt1. 
    eapply H.
    eapply H8.

    exists tl_upper_bound.

  
End TwoThreeTreesWF.