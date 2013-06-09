Require Import FP.CoreClasses.
Require Import FP.CoreData.
Require Import FP.Classes.
Require Import FP.Data.TwoThreeTrees.
Require Import FP.Data.Extend.
Require Import FP.Data.Option.
Require Import FP.Data.Prod.
Require Import FP.Data.Sum.

Import CoreClassesNotation.
Import CoreDataNotation.
Import ClassesNotation.


Module TwoThreeTreesWF.
  Import TwoThreeTrees.

  Section Context.
    Context {K V:Type}
      `{! Lte K ,! Eqv K ,! ER_WF K ,! TotalOrd K ,! TotalOrdDec K ,! TotalOrd_RDC K
       ,! Lattice K ,! BoundedLattice K ,! LatticeWF K ,! BoundedLatticeWF K
       }.

    Inductive in_tree : K -> tree K V -> Prop :=
      | InTwoLeftTree :
          forall k tl pm tr,
          in_tree k tl
          -> in_tree k (Two_t tl pm tr)
      | InTwoRightTree :
          forall k tl pm tr,
          in_tree k tr
          -> in_tree k (Two_t tl pm tr)
      | InTwoNode :
          forall k tl km vm tr,
          k ~= km
          -> in_tree k (Two_t tl (km,vm) tr)
      | InThreeLeftTree :
          forall k tl pl tm pr tr,
          in_tree k tl
          -> in_tree k (Three_t tl pl tm pr tr)
      | InThreeMiddleTree :
          forall k tl pl tm pr tr,
          in_tree k tm
          -> in_tree k (Three_t tl pl tm pr tr)
      | InThreeRightTree :
          forall k tl pl tm pr tr,
          in_tree k tr
          -> in_tree k (Three_t tl pl tm pr tr)
      | InThreeLeftNode :
          forall k tl kl vl tm pr tr,
          k ~= kl
          -> in_tree k (Three_t tl (kl,vl) tm pr tr)
      | InThreeRightNode :
          forall k tl pl tm kr vr tr,
          k ~= kr ->
          in_tree k (Three_t tl pl tm (kr,vr) tr).
    Hint Constructors in_tree.

    Instance in_tree_Proper : Proper (eqv ==> eq ==> Basics.impl) in_tree.
    Proof.
      unfold Proper,"==>",Basics.impl ; intros x y xyeqv t1 t2 teq int.
      generalize dependent y.
      generalize dependent t2.
      induction int ; intros ; subst
      ; repeat
          match goal with
          | [ H1 : ?y ~= ?x , H2 : ?y ~= ?z |- in_tree ?x _ ] =>
              assert (x ~= z) ; [transitivity y ; [symmetry|] ; auto |] ; clear H1 H2
          | _ => eauto
          end.
    Qed.

    Definition in_two_node_lib :
      forall {tl km vm tr}, in_tree km (Two_t tl (km,vm) tr).
    Proof. intros ; eapply InTwoNode ; reflexivity. Qed.
    Hint Resolve in_two_node_lib.

    Definition in_three_left_node_lib :
      forall {tl kl vl tm pr tr},
        in_tree kl (Three_t tl (kl,vl) tm pr tr).
    Proof. intros ; eapply InThreeLeftNode ; reflexivity. Qed.
    Hint Resolve in_three_left_node_lib.

    Definition in_three_right_node_lib :
      forall {tl pl tm kr vr tr},
        in_tree kr (Three_t tl pl tm (kr,vr) tr).
    Proof. intros ; eapply InThreeRightNode ; reflexivity. Qed.
    Hint Resolve in_three_right_node_lib.

    Inductive tree_iwf : extend K -> extend K -> N -> tree K V -> Prop :=
      | NullWF :
          forall {t_lower_bound t_upper_bound},
          t_lower_bound <= t_upper_bound
          -> tree_iwf t_lower_bound t_upper_bound 0 Null_t
      | TwoWF :
          forall
            {tl tl_lower_bound tl_upper_bound
             tr tr_lower_bound tr_upper_bound
             t_height
             km vm},
          tree_iwf tl_lower_bound tl_upper_bound t_height tl
          -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
          -> tl_upper_bound <= Extend km <= tr_lower_bound
          -> tree_iwf tl_lower_bound tr_upper_bound (t_height+1)
                      (Two_t tl (km,vm) tr)
      | ThreeWF :
          forall
            {tl tl_lower_bound tl_upper_bound
             tm tm_lower_bound tm_upper_bound
             tr tr_lower_bound tr_upper_bound
             t_height
             kl vl kr vr},
          tree_iwf tl_lower_bound tl_upper_bound t_height tl
          -> tree_iwf tm_lower_bound tm_upper_bound t_height tm
          -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
          -> tl_upper_bound <= Extend kl <= tm_lower_bound
          -> tm_upper_bound <= Extend kr <= tr_lower_bound
          -> tree_iwf tl_lower_bound tr_upper_bound (t_height+1)
                      (Three_t tl (kl,vl) tm (kr,vr) tr).
    Hint Constructors tree_iwf.

    Lemma tree_iwf_weaken :
      forall t t_lower t_upper t_height t_lower' t_upper',
      tree_iwf t_lower t_upper t_height t
      -> t_lower' <= t_lower
      -> t_upper <= t_upper'
      -> tree_iwf t_lower' t_upper' t_height t.
    Proof.
      intros t ; induction t ; intros
      ; repeat
          match goal with
          | [ |- tree_iwf _ _ _ Null_t ] => constructor
          | [ |- tree_iwf _ _ _ (Two_t _ _ _) ] => econstructor
          | [ |- tree_iwf _ _ _ (Three_t _ _ _ _ _) ] => econstructor
          | [ H : tree_iwf _ _ _ Null_t |- _ ] => inversion H ; subst ; clear H
          | [ H : tree_iwf _ _ _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
          | [ H : tree_iwf _ _ _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
          | [ H1 : ?a <= ?b , H2 : ?b <= ?c , H3 : ?c <= ?d |- ?a <= ?d ] =>
              transitivity b ; [auto|] ; transitivity c ; [auto|] ; auto
          | _ => auto
          end ; eauto
      ; match goal with
          | [ IH : forall _ _ _ _ _, _ -> _ -> _ -> tree_iwf _ _ _ ?t
            , H : tree_iwf ?t_lower _ _ ?t
            |- tree_iwf ?t_lower _ _ ?t
            ] => eapply IH
          | [ IH : forall _ _ _ _ _, _ -> _ -> _ -> tree_iwf _ _ _ ?t
            , H : tree_iwf _ ?t_upper _ ?t
            |- tree_iwf _ ?t_upper _ ?t
            ] => eapply IH
          | _ => auto
      end ; eauto ; try reflexivity.
    Qed.

    Lemma null_t_eqv : forall {b}, tree_iwf b b 0 Null_t.
    Proof.
      intros ; econstructor ; reflexivity.
    Qed.
    Hint Resolve null_t_eqv.

    Lemma tree_iwf_0height :
      forall {tlb tub t}, tree_iwf tlb tub 0 t -> t = Null_t.
    Proof.
      intros ; inversion H ; auto ; destruct t_height ; unfold "+" in * ; simpl in * ; congruence.
    Qed.

    Lemma tree_iwf_ineq :
      forall {t_lower t_upper t_height t},
      tree_iwf t_lower t_upper t_height t
      -> t_lower <= t_upper.
    Proof.
      intros * * * * H ; induction H ; auto
      ; repeat
          match goal with
          | [ H : _ <= _ <= _ |- _ ] => destruct H
          | [ H : ?x <= ?y |- ?x <= ?z ] => transitivity y ; auto
          | _ => auto
          end
      ; eauto.
    Qed.

    Lemma in_wf_tree :
      forall
        {t:tree K V}
        {t_lower t_upper t_height},
      tree_iwf t_lower t_upper t_height t
      -> forall k, in_tree k t
      -> t_lower <= Extend k <= t_upper.
    Proof.
      intros t t_lower t_upper t_height tiwf ; induction tiwf ; intros
      ; repeat 
          match goal with
          | [ |- ?x ~= ?x ] => reflexivity
          | [ H : ?x ~= ?y |- ?G ?y ~= ?G ?x ] => rewrite H
          | [ H : _ <= _ <= _ |- _ ] => destruct H
          | [ H : in_tree _ Null_t |- _ ] => inversion H
          | [ H : tree_iwf _ _ _ ?t |- _ ] => apply tree_iwf_ineq in H
          | [ H : ?k ~= ?k' |- ?l <= Extend ?k ] =>
            refine (PartialOrd_respect_eqv l l (reflexivity l) (Extend k') (Extend k) _ _)
            ; [rewrite H ; reflexivity|]
          | [ H : ?k ~= ?k' |- Extend ?k <= ?u ] =>
            refine (PartialOrd_respect_eqv (Extend k') (Extend k) _ u u (reflexivity u) _ )
            ; [rewrite H ; reflexivity|]
          | [ H : in_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
          | [ H : in_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
          | [ IH : forall k, in_tree k ?t -> _ , H : in_tree ?k ?t |- _ ] => specialize (IH k H)
          | [ H1 : ?a <= ?b , H2 : ?b <= ?c |- ?a <= ?c ] =>
            transitivity b ; auto
          | [ H1 : ?a <= ?b , H2 : ?b <= ?c , H3 : ?c <= ?d , H4 : ?d <= ?e |- ?a <= ?e ] =>
            transitivity b ; [auto|] ; transitivity c ; [auto|] ; transitivity d ; auto
          | [ H1 : ?a <= ?b , H2 : ?b <= ?c , H3 : ?c <= ?d , H4 : ?d <= ?e , H5 : ?e <= ?f
            |- ?a <= ?f ] =>
            transitivity b ; [auto|] ; transitivity c ; [auto|] ; transitivity d ; [auto|]
            ; transitivity e ; auto
          | [ H1 : ?a <= ?b , H2 : ?b <= ?c , H3 : ?c <= ?d , H4 : ?d <= ?e , H5 : ?e <= ?f
            , H6 : ?f <= ?g , H7 : ?g <= ?h
            |- ?a <= ?h ] =>
              transitivity b ; [auto|] ; transitivity c ; [auto|] ; transitivity d ; [auto|]
              ; transitivity e ; [auto|] ; transitivity f ; [auto|] ; transitivity g ; auto
          | [ |- _ <= _ <= _ ] => constructor
          | _ => auto
          end.
    Qed.

    Inductive in_context : K -> context K V -> Prop :=
      | InTwoLeftHoleContext :
          forall k pm tr c,
          in_context k c
          -> in_context k (TwoLeftHole_c pm tr c)
      | InTwoLeftHoleTree :
          forall k pm tr c,
          in_tree k tr
          -> in_context k (TwoLeftHole_c pm tr c)
      | InTwoLeftHoleNode :
          forall k km vm tr c,
          k ~= km
          -> in_context k (TwoLeftHole_c (km,vm) tr c)
      | InTwoRightHoleContext :
          forall k tl pm c,
          in_context k c
          -> in_context k (TwoRightHole_c tl pm c)
      | InTwoRightHoleTree :
          forall k tl pm c,
          in_tree k tl
          -> in_context k (TwoRightHole_c tl pm c)
      | InTwoRightHoleNode :
          forall k tl km vm c,
          k ~= km
          -> in_context k (TwoRightHole_c tl (km,vm) c)
      | InThreeLeftHoleContext :
          forall k pl tm pr tr c,
          in_context k c
          -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | InThreeLeftHoleMiddleTree :
          forall k pl tm pr tr c,
          in_tree k tm
          -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | InThreeLeftHoleRightTree :
          forall k pl tm pr tr c,
          in_tree k tr
          -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | InThreeLeftHoleLeftNode :
          forall k kl vl tm pr tr c,
          k ~= kl
          -> in_context k (ThreeLeftHole_c (kl,vl) tm pr tr c)
      | InThreeLeftHoleRightNode :
          forall k pl tm kr vr tr c,
          k ~= kr
          -> in_context k (ThreeLeftHole_c pl tm (kr,vr) tr c)
      | InThreeMiddleHoleContext :
          forall k tl pl pr tr c,
          in_context k c
          -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | InThreeMiddleHoleLeftTree :
          forall k tl pl pr tr c,
          in_tree k tl
          -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | InThreeMiddleHoleRightTree :
          forall k tl pl pr tr c,
          in_tree k tr
          -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | InThreeMiddleHoleLeftNode :
          forall k tl kl vl pr tr c,
          k ~= kl
          -> in_context k (ThreeMiddleHole_c tl (kl,vl) pr tr c)
      | InThreeMiddleHoleRightNode :
          forall k tl pl kr vr tr c,
          k ~= kr
          -> in_context k (ThreeMiddleHole_c tl pl (kr,vr) tr c)
      | InThreeRightHoleContext :
          forall k tl pl tm pr c,
          in_context k c
          -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | InThreeRightHoleLeftTree :
          forall k tl pl tm pr c,
          in_tree k tl
          -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | InThreeRightHoleMiddleTree :
          forall k tl pl tm pr c,
          in_tree k tm
          -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | InThreeRightHoleLeftNode :
          forall k tl kl vl tm pr c,
          k ~= kl
          -> in_context k (ThreeRightHole_c tl (kl,vl) tm pr c)
      | InThreeRightHoleRightNode :
          forall k tl pl tm kr vr c,
          k ~= kr
          -> in_context k (ThreeRightHole_c tl pl tm (kr,vr) c).
    Hint Constructors in_context.
            
    Inductive context_iwf :
          extend K -> extend K -> N (* bounds and height of hole *)
          -> extend K -> extend K -> N (* bounds and height when filled *)
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
          -> h_upper_bound <= Extend k <= tr_lower_bound
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
          -> tl_upper_bound <= Extend k <= h_lower_bound
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
          -> h_upper_bound <= Extend kl <= tm_lower_bound
          -> tm_upper_bound <= Extend kr <= tr_lower_bound
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
          -> tl_upper_bound <= Extend kl <= h_lower_bound
          -> h_upper_bound <= Extend kr <= tr_lower_bound
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
          -> tl_upper_bound <= Extend kl <= tm_lower_bound
          -> tm_upper_bound <= Extend kr <= h_lower_bound
          -> context_iwf h_lower_bound h_upper_bound h_height
                         c_lower_bound c_upper_bound c_height
                         (ThreeRightHole_c tl (kl,vl) tm (kr,vr) c).
    Hint Constructors context_iwf.

  Inductive in_location : K -> location K V -> Prop :=
    | InLocTwoHoleContext :
        forall k tl tr c,
        in_context k c
        -> in_location k (TwoHole_l tl tr c)
    | InLocTwoHoleLeftTree :
        forall k tl tr c,
        in_tree k tl
        -> in_location k (TwoHole_l tl tr c)
    | InLocTwoHoleRightTree :
        forall k tl tr c,
        in_tree k tr
        -> in_location k (TwoHole_l tl tr c)
    | InLocThreeLeftHoleContext :
        forall k tl tm pr tr c,
        in_context k c
        -> in_location k (ThreeLeftHole_l tl tm pr tr c)
    | InLocThreeLeftHoleLeftTree :
        forall k tl tm pr tr c,
        in_tree k tl
        -> in_location k (ThreeLeftHole_l tl tm pr tr c)
    | InLocThreeLeftHoleMiddleTree :
        forall k tl tm pr tr c,
        in_tree k tm
        -> in_location k (ThreeLeftHole_l tl tm pr tr c)
    | InLocThreeLeftHoleRightTree :
        forall k tl tm pr tr c,
        in_tree k tr
        -> in_location k (ThreeLeftHole_l tl tm pr tr c)
    | InLocThreeLeftHoleNode :
        forall k tl tm kr vr tr c,
        k ~= kr
        -> in_location k (ThreeLeftHole_l tl tm (kr,vr) tr c)
    | InLocThreeRightHoleContext :
        forall k tl pl tm tr c,
        in_context k c
        -> in_location k (ThreeRightHole_l tl pl tm tr c)
    | InLocThreeRightHoleLeftTree :
        forall k tl pl tm tr c,
        in_tree k tl
        -> in_location k (ThreeRightHole_l tl pl tm tr c)
    | InLocThreeRightHoleMiddleTree :
        forall k tl pl tm tr c,
        in_tree k tm
        -> in_location k (ThreeRightHole_l tl pl tm tr c)
    | InLocThreeRightHoleRightTree :
        forall k tl pl tm tr c,
        in_tree k tr
        -> in_location k (ThreeRightHole_l tl pl tm tr c)
    | InLocThreeRightHoleNode :
        forall k tl kl vl tm tr c,
        k ~= kl
        -> in_location k (ThreeRightHole_l tl (kl,vl) tm tr c).
  Hint Constructors in_location.

  Inductive location_iwf :
        extend K -> extend K (* bounds of hole *)
        -> extend K -> extend K -> N (* bounds and height when filled *)
        -> location K V
        -> Prop :=
    | LocTwoHoleWF :
        forall
          t_height
          tl tl_lower_bound tl_upper_bound
          tr tr_lower_bound tr_upper_bound
          c c_lower_bound c_upper_bound c_height,
        tree_iwf tl_lower_bound tl_upper_bound t_height tl
        -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
        -> context_iwf tl_lower_bound tr_upper_bound (t_height+1)
                       c_lower_bound c_upper_bound c_height c
        -> location_iwf tl_upper_bound tr_lower_bound
                        c_lower_bound c_upper_bound c_height
                        (TwoHole_l tl tr c)
    | LocThreeLeftHoleWF :
        forall
          t_height
          tl tl_lower_bound tl_upper_bound
          tm tm_lower_bound tm_upper_bound
          tr tr_lower_bound tr_upper_bound
          c c_lower_bound c_upper_bound c_height
          kr vr,
        tree_iwf tl_lower_bound tl_upper_bound t_height tl
        -> tree_iwf tm_lower_bound tm_upper_bound t_height tm
        -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
        -> tm_upper_bound <= Extend kr <= tr_lower_bound
        -> context_iwf tl_lower_bound tr_upper_bound (t_height+1)
                       c_lower_bound c_upper_bound c_height c
        -> location_iwf tl_upper_bound tm_lower_bound
                        c_lower_bound c_upper_bound c_height
                        (ThreeLeftHole_l tl tm (kr,vr) tr c)
    | LocThreeRightHoleWF :
        forall
          t_height
          tl tl_lower_bound tl_upper_bound
          tm tm_lower_bound tm_upper_bound
          tr tr_lower_bound tr_upper_bound
          c c_lower_bound c_upper_bound c_height
          kl vl,
        tree_iwf tl_lower_bound tl_upper_bound t_height tl
        -> tree_iwf tm_lower_bound tm_upper_bound t_height tm
        -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
        -> tl_upper_bound <= Extend kl <= tm_lower_bound
        -> context_iwf tl_lower_bound tr_upper_bound (t_height+1)
                       c_lower_bound c_upper_bound c_height c
        -> location_iwf tm_upper_bound tr_lower_bound
                        c_lower_bound c_upper_bound c_height
                        (ThreeRightHole_l tl (kl,vl) tm  tr c).
  Hint Constructors location_iwf.
            
  Global Instance tree_WellFormed : WellFormed (tree K V) :=
    { wf :=
        fun (t:tree K V) =>
        exists (n:N) (lb:extend K) (ub:extend K),
        tree_iwf lb ub n t
    }.

  Local Ltac mysimp :=
    match goal with
    | [ |- forall  _, _ ] => intros
    | [ H : and _ _ |- _ ] => destruct H
    | [ H : inl _ = inr _ |- _ ] => discriminate H
    | [ H : inr _ = inr _ |- _ ] => inversion H ; subst ; clear H
    | [ H : ?a <= ?b <= ?c |- ?a <= ?b ] => apply H
    | [ H : ?a <= ?b <= ?c |- ?b <= ?c ] => apply H
    | [ H1 : ?X, H2 : ?X -> ?Y |- ?Y ] => apply (H2 H1)
    | [ H1 : ?x ~= ?z, H2 : ?y ~= ?z, H3 : ?x /~= ?y |- _ ] =>
        exfalso ; apply H3 ; transitivity z ; [ apply H1 | symmetry ; apply H2 ]
    | [ H1 : ?x ~= ?y, H2 : ?y /~= ?x |- _ ] => symmetry in H1 ; contradiction
    | [ H : (_,_) = ?p |- _ ] => destruct p
    | [ |- context [ let (_,_) := ?p in _ ] ] => destruct p
    | [ H : in_tree _ Null_t |- _ ] => inversion H
    | [ H : in_context _ Top_c |- _ ] => inversion H
    | [ H : tree_iwf _ _ _ Null_t |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : tree_iwf _ _ _ (Two_t _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : tree_iwf _ _ _ (Three_t _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : tree_iwf _ _ 0 _ |- _ ] =>
        rewrite (tree_iwf_0height H) in * ; inversion H ; subst ; clear H
    | [ H : in_tree _ (Two_t Null_t _ Null_t) |- _ ] => inversion H ; subst ; clear H
    | [ H : ?n + 1 = 0 |- _ ] => destruct n ; unfold "+" in H ; simpl in H ; discriminate H
    | [ H : 0 = ?n + 1  |- _ ] => destruct n ; unfold "+" in H ; simpl in H ; discriminate H
    | _ => auto
    end.

  Local Ltac rip :=
    match goal with
    | [ H : in_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
    | [ H : in_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
    | [ H : in_context _ (TwoLeftHole_c _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ (TwoRightHole_c _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ (ThreeRightHole_c _ _ _ _ _) |- _ ] =>
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
    | [ H : in_location _ (TwoHole_l _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_location _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_location _ (ThreeRightHole_l _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : location_iwf _ _ _ _ _ (TwoHole_l _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : location_iwf _ _ _ _ _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : location_iwf _ _ _ _ _ (ThreeRightHole_l _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | _ => auto
    end.


  Lemma zip_in :
    forall {c:context K V} {t:tree K V} {k:K},
    (in_context k c -> in_tree k (zip t c))
    /\ (in_tree k t -> in_tree k (zip t c)).
  Proof.
    intros c ; induction c ; simpl ; repeat mysimp ; constructor ; repeat mysimp ; repeat rip
    ; match goal with
      | [ IH : forall t k, and _ _ |- in_tree ?k (zip ?t ?c) ] =>
          match goal with
          | [ H : in_context ?k _ |- _ ] => specialize (IH t k)
          | [ H : in_tree ?k _ |- _ ] => specialize (IH t k)
          | [ H : ?k ~= _ |- _ ] => specialize (IH t k)
          end
    end ; repeat mysimp ; eauto.
  Qed.
  Lemma zip_in_context :
    forall {c:context K V} {t:tree K V} {k:K},
    in_context k c -> in_tree k (zip t c).
  Proof. apply @zip_in. Qed.
  Hint Resolve zip_in_context.
  Lemma zip_in_tree :
    forall {c:context K V} {t:tree K V} {k:K},
    in_tree k t -> in_tree k (zip t c).
  Proof. apply @zip_in. Qed.
  Hint Resolve zip_in_tree.


  Lemma zip_wf :
    forall 
      {c:context K V} {t:tree K V}
      {t_lower_bound t_upper_bound t_height
       c_lower_bound c_upper_bound c_height},
    tree_iwf t_lower_bound t_upper_bound t_height t
    -> context_iwf t_lower_bound t_upper_bound t_height
                   c_lower_bound c_upper_bound c_height c
    -> tree_iwf c_lower_bound c_upper_bound c_height (zip t c).
  Proof.
    intros c ; induction c ; repeat mysimp ; repeat rip ; eapply IHc ; eauto.
  Qed.
  Hint Resolve zip_wf.

  Lemma fuse_in :
    forall {c1:context K V} {c2:context K V} {k},
    (in_context k c1 -> in_context k (fuse c1 c2))
    /\ (in_context k c2 -> in_context k (fuse c1 c2)).
  Proof.
    intros c ; induction c ; simpl ; repeat mysimp ; constructor ; repeat mysimp ; repeat rip
    ; match goal with
      | [ IH : forall c2 k, and _ _ , H : in_context ?k _ |- context [ fuse ?c ?c2 ]] =>
          specialize (IH c2 k)
      end
    ; repeat mysimp ; eauto.
  Qed.
  Lemma fuse_in_context1 :
    forall {c1:context K V} {c2:context K V} {k},
    in_context k c1 -> in_context k (fuse c1 c2).
  Proof. apply @fuse_in. Qed.
  Hint Resolve fuse_in_context1.
  Lemma fuse_in_context2 :
    forall {c1:context K V} {c2:context K V} {k},
    in_context k c2 -> in_context k (fuse c1 c2).
  Proof. apply @fuse_in. Qed.
  Hint Resolve fuse_in_context2.

  Lemma fuse_wf :
    forall
      {c1:context K V} {c2:context K V}
      {c1h_lower_bound c1h_upper_bound c1h_height
       c1_lower_bound c1_upper_bound c1_height
       c2_lower_bound c2_upper_bound c2_height},
    context_iwf c1h_lower_bound c1h_upper_bound c1h_height
                c1_lower_bound c1_upper_bound c1_height c1
    -> context_iwf c1_lower_bound c1_upper_bound c1_height
                  c2_lower_bound c2_upper_bound c2_height c2
    -> context_iwf c1h_lower_bound c1h_upper_bound c1h_height
                   c2_lower_bound c2_upper_bound c2_height (fuse c1 c2).
  Proof.
    intros c1 ; induction c1 ; simpl ; repeat mysimp ; repeat rip ; eauto.
  Qed.
  Hint Resolve fuse_wf.

  Lemma fill_location_in :
    forall {l:location K V} {k:K} {v:V},
    (in_tree k (fill_location (k,v) l))
    /\ (forall k', in_location k' l -> in_tree k' (fill_location (k,v) l)).
  Proof.
    intros l ; induction l ; simpl ; repeat mysimp ; constructor ; repeat mysimp ; repeat rip.
  Qed.
  Lemma fill_location_in_filled :
    forall {l:location K V} {k:K} {v:V},
    in_tree k (fill_location (k,v) l).
  Proof. intros ; apply (proj1 fill_location_in). Qed.
  Hint Resolve fill_location_in_filled.
  Lemma fill_location_in_tree :
    forall {l:location K V} {k:K} {v:V} {k':K},
    in_location k' l -> in_tree k' (fill_location (k,v) l).
  Proof. intros * * * * H ; apply (proj2 fill_location_in _ H). Qed.
  Hint Resolve fill_location_in_tree.

  Lemma fill_location_wf :
    forall
      {l:location K V} {k:K} {v:V}
      {h_lower_bound h_upper_bound
       c_lower_bound c_upper_bound c_height},
    h_lower_bound <= Extend k <= h_upper_bound
    -> location_iwf h_lower_bound h_upper_bound
                    c_lower_bound c_upper_bound c_height l
    -> tree_iwf c_lower_bound c_upper_bound c_height (fill_location (k,v) l).
  Proof.
    intros l ; induction l ; intros ; repeat mysimp ; repeat rip ; eapply zip_wf
    ; eauto.
  Qed.
  Hint Resolve fill_location_wf.

  Lemma locate_in :
    forall (t:tree K V) (k:K) (c:context K V),
    match locate k t c with
    | inl c' =>
        forall k',
        (in_tree k' t -> in_context k' c')
        /\ (in_context k' c -> in_context k' c')
    | inr ((k',_),l) =>
        k ~= k'
        /\ (forall k'',
            k /~= k''
            -> (in_tree k'' t -> in_location k'' l)
               /\ (in_context k'' c -> in_location k'' l))
    end.
  Proof.
    intros t ; induction t ; intros ; simpl ; repeat mysimp
    ; repeat
        match goal with
        | [ |- and _ _ ] => constructor
        | [ |- context[ ?x <=>! ?y ] ] =>
            let cmp := fresh "cmp" in
            remember (x <=>! y) as cmp
            ; match goal with
              [ cmp_eqn : _ = x <=>! y |- _ ] =>
                symmetry in cmp_eqn
                ; destruct cmp
                ; [ apply tord_dec_correct_eqv in cmp_eqn
                  | apply tord_dec_correct_lt in cmp_eqn
                  | apply tord_dec_correct_gt in cmp_eqn
                  ]
              end
        | [ IH : forall k c, match locate k ?t c with _ => _ end |- match locate ?k ?t ?c with _ => _ end ] =>
            specialize (IH k c) ; remember (locate k t c) as m ; destruct m
        | [ IH : forall k:K, and _ _  |- in_context ?k _ ] => specialize (IH k)
        | [ IH : forall k:K, ?k' /~= k -> and _ _  , H : ?k' /~= ?k |- _ ] => specialize (IH k H)
        | [ |- ~ _ ] => unfold "~" ; intros
        | _ => mysimp
        end ; repeat rip ; repeat mysimp ; eauto.
  Qed.

  Lemma locate_not_in :
    forall
      {t} k c
      {t_lower t_upper t_height},
    tree_iwf t_lower t_upper t_height t
    -> match locate k t c with
       | inl _ => ~ in_tree k t
       | inr _ => True
       end.
  Proof.
    intros t ; induction t ; intros ; simpl ; repeat mysimp
    ; repeat
        match goal with
        | [ |- ~ _ ] => unfold "~" at 1 ; intros
        | [ |- context[ ?x <=>! ?y ] ] =>
            let cmp := fresh "cmp" in
            remember (x <=>! y) as cmp
            ; match goal with
              [ cmp_eqn : _ = x <=>! y |- _ ] =>
                symmetry in cmp_eqn
                ; destruct cmp
                ; [ apply tord_dec_correct_eqv in cmp_eqn
                  | apply tord_dec_correct_lt in cmp_eqn
                  | apply tord_dec_correct_gt in cmp_eqn
                  ]
              end
        | [ IH : forall k c t_lower t_upper t_height,
                 _ -> match locate k ?t c with _ => _ end
          , Ht : tree_iwf ?t_lower ?t_upper ?t_height ?t
          |- match locate ?k ?t ?c with _ => _ end ] =>
            specialize (IH k c _ _ _ Ht)
            ; remember (locate k t c) as m ; destruct m
        | [ IH : forall k c t_lower t_upper t_height c_lower c_upper c_height,
                 _ -> _ -> match locate k ?t c with _ => _ end
          , Ht : tree_iwf ?t_lower ?t_upper ?t_height ?t
          , Hc : context_iwf _ _ (?t_height + 1) ?c_lower ?c_upper ?c_height _ 
          |- match locate ?k ?t ?c with _ => _ end ] =>
            let Hc' := fresh "Hc" in
            assert (context_iwf t_lower t_upper t_height c_lower c_upper c_height c) as Hc' ; [eauto|]
            ; specialize (IH k c _ _ _ _ _ _ Ht Hc')
            ; remember (locate k t c) as m ; destruct m
        | _ => mysimp
        end
    ; repeat
        match goal with
        | [ H : in_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
        | [ H : in_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
        end
    ; repeat
        match goal with
        | [ Hp : ?X , Hn : ~ ?X |- _ ] => contradiction
        | [ H : ?x < ?x |- _ ] => destruct H ; contradiction
        | [ H_in : in_tree ?k ?t , H_iwf : tree_iwf ?l ?u ?h ?t |- _ ] => 
            apply (in_wf_tree H_iwf) in H_in
        | [ H : tree_iwf ?l ?u ?h ?t |- _ ] => apply tree_iwf_ineq in H
        | [ H: ?k < _ |- _ ] =>
            match type of k with
            | K => apply (InjectionRespect_eta (inj:=Extend)) in H
            | _ => fail 1
            end
        | [ H: ?k ~= _ |- _ ] =>
            match type of k with
            | K => apply (InjectionRespect_eta (inj:=Extend)) in H
            | _ => fail 1
            end
        | [ Heq : ?x ~= ?y , H : ?x < ?z |- _ ] => rewrite Heq in H
        | [ Heq : ?y ~= ?z , H : ?x < ?y |- _ ] => rewrite Heq in H
        | [ H1 : ?a <= ?b , H2 : ?b <= ?c , H3 : ?c < ?a |- _ ] =>
            destruct H3 as [Ht Hf] ; apply Hf ; transitivity b ; auto
        | [ H1 : ?a <= ?b , H2 : ?b <= ?c , H3 : ?c <= ?d , H4 : ?d <= ?e
          , H5 : ?e <= ?f , H6 : ?f < ?a |- _ ] =>
              destruct H6 as [Ht Hf] ; apply Hf
              ; transitivity b ; [auto|] ; transitivity c ; [auto|] ; transitivity d ; [auto|]
              ; transitivity e ; auto
        | [ H1 : ?a <= ?b , H2 : ?b <= ?c , H3 : ?c <= ?d , H4 : ?d < ?a |- _ ] =>
              destruct H4 as [Ht Hf] ; apply Hf
              ; transitivity b ; [auto|] ; transitivity c ; auto
        | _ => mysimp
        end.
  Qed.

  Lemma locate_wf :
    forall
      (t:tree K V) (k:K) (c:context K V)
      t_lower_bound t_upper_bound t_height
      c_lower_bound c_upper_bound c_height,
    tree_iwf t_lower_bound t_upper_bound t_height t
    -> context_iwf t_lower_bound t_upper_bound t_height
                   c_lower_bound c_upper_bound c_height c
    -> exists h_lower_bound h_upper_bound,
       match locate k t c with
       | inl c =>
           context_iwf h_lower_bound h_upper_bound 0
                       c_lower_bound c_upper_bound c_height c
       | inr ((_,_),l) =>
           location_iwf h_lower_bound h_upper_bound
                        c_lower_bound c_upper_bound c_height l
       end.
  Proof.
    intros t ; induction t ; intros ; simpl ; repeat mysimp
    ; repeat
        match goal with
        | [ |- context[ ?x <=>! ?y ] ] =>
            let cmp := fresh "cmp" in
            remember (x <=>! y) as cmp
            ; match goal with
              [ cmp_eqn : _ = x <=>! y |- _ ] =>
                symmetry in cmp_eqn
                ; destruct cmp
                ; [ apply tord_dec_correct_eqv in cmp_eqn
                  | apply tord_dec_correct_lt in cmp_eqn
                  | apply tord_dec_correct_gt in cmp_eqn
                  ]
              end
        | _ => auto
        end ; eauto.
  Qed.

  Lemma locate_greatest_in :
    forall (t:tree K V) (c:context K V),
    match locate_greatest t c with
    | None => t = Null_t
    | Some ((k,_),lM) =>
        let l :=
          match lM with
          | inl c => TwoHole_l Null_t Null_t c
          | inr (el,c) => ThreeRightHole_l Null_t el Null_t Null_t c
          end
        in
        forall k',
        k /~= k'
        -> (forall t_lower t_upper t_height,
            in_tree k' t
            -> tree_iwf t_lower t_upper t_height t -> in_location k' l)
           /\ (in_context k' c -> in_location k' l)
    end.
  Proof.
    intros t ; induction t ; intros ; simpl ; repeat mysimp.
    - specialize (IHt2 (TwoRightHole_c t1 p c)).
      remember (locate_greatest t2 (TwoRightHole_c t1 p c)) as m ; destruct m ; simpl in *
      ; unfold mtry ; simpl ; repeat mysimp.
      + specialize (IHt2 k' H) ; repeat mysimp ; constructor ; repeat mysimp.
        inversion H2 ; subst ; clear H2
        ; match goal with
          | [ H : context [ ?G ] |- ?G ] => eapply H ; eauto ; fail
          end.
      + rewrite IHt2 in * ; clear IHt2 ; constructor ; repeat mysimp.
    - specialize (IHt3 (ThreeRightHole_c t1 p t2 p0 c)).
      remember (locate_greatest t3 (ThreeRightHole_c t1 p t2 p0 c)) as m ; destruct m ; simpl in *
      ; unfold mtry ; simpl ; repeat mysimp.
      + specialize (IHt3 k' H) ; repeat mysimp ; constructor ; repeat mysimp.
        inversion H2 ; subst ; clear H2
        ; match goal with
          | [ H : context [ ?G ] |- ?G ] => eapply H ; eauto ; fail
          end.
      + rewrite IHt3 in * ; clear IHt3 ; constructor ; repeat mysimp.
        inversion H0 ; subst ; clear H0 ; repeat mysimp.
  Qed.

  Lemma locate_greatest_in_result :
    forall t c,
    match locate_greatest t c with
    | None => t = Null_t
    | Some ((k,_),_) => in_tree k t
    end.
  Proof.
    intros t ; induction t ; intros ; simpl ; auto.
    - specialize (IHt2 (TwoRightHole_c t1 p c))
      ; remember (locate_greatest t2 (TwoRightHole_c t1 p c)) as m ; destruct m ; simpl ; repeat mysimp.
    - specialize (IHt3 (ThreeRightHole_c t1 p t2 p0 c))
      ; remember (locate_greatest t3 (ThreeRightHole_c t1 p t2 p0 c)) as m ; destruct m ; simpl ; repeat mysimp.
  Qed.

  Lemma locate_greatest_wf :
    forall
      (t:tree K V) (c:context K V)
      t_lower_bound t_upper_bound t_height
      c_lower_bound c_upper_bound c_height,
    tree_iwf t_lower_bound t_upper_bound t_height t
    -> context_iwf t_lower_bound t_upper_bound t_height
                   c_lower_bound c_upper_bound c_height c
    -> match locate_greatest t c with
       | None => t = Null_t
       | Some (_,lM) =>
           let l :=
             match lM with
             | inl c => TwoHole_l Null_t Null_t c
             | inr (el,c) => ThreeRightHole_l Null_t el Null_t Null_t c
             end
           in
           exists h_lower_bound h_upper_bound,
           location_iwf h_lower_bound h_upper_bound
                        c_lower_bound c_upper_bound c_height l
       end.
  Proof.
    intros t ; induction t ; intros ; simpl ; repeat mysimp.
    - specialize (IHt2 (TwoRightHole_c t1 (km, vm) c)
                       tr_lower_bound t_upper_bound t_height0
                       c_lower_bound c_upper_bound c_height
                       H8).
      cut (context_iwf tr_lower_bound t_upper_bound t_height0
                       c_lower_bound c_upper_bound c_height
                       (TwoRightHole_c t1 (km,vm) c))
      ; [intros cwf ; specialize (IHt2 cwf)|] ; repeat mysimp ; eauto.
      remember (locate_greatest t2 (TwoRightHole_c t1 (km,vm) c)) as m
      ; destruct m ; simpl in *
      ; unfold mtry ; simpl ; repeat mysimp.
      rewrite IHt2 in * ; clear IHt2 ; repeat mysimp.
      exists t_lower_bound , t_upper_bound ; eauto.
    - specialize (IHt3 (ThreeRightHole_c t1 (kl,vl) t2 (kr,vr) c)
                       tr_lower_bound t_upper_bound t_height0
                       c_lower_bound c_upper_bound c_height
                       H11).
      cut (context_iwf tr_lower_bound t_upper_bound t_height0
                       c_lower_bound c_upper_bound c_height
                       (ThreeRightHole_c t1 (kl,vl) t2 (kr,vr) c))
      ; [intros cwf ; specialize (IHt3 cwf)|] ; repeat mysimp ; eauto.
      remember (locate_greatest t3 (ThreeRightHole_c t1 (kl,vl) t2 (kr,vr) c)) as m
      ; destruct m ; simpl in *
      ; unfold mtry ; simpl ; repeat mysimp.
      rewrite IHt3 in * ; clear IHt3 ; repeat mysimp.
      exists (Extend kl) , t_upper_bound ; eauto.
      econstructor ; eauto.
      constructor ; [transitivity tl_upper_bound ; auto | reflexivity].
  Qed.

  Lemma insert_up_in :
    forall c tl k v tr,
    let t := insert_up (tl,(k,v),tr) c in
    forall k',
    (k' ~= k -> in_tree k' t)
    /\ (in_tree k' tl -> in_tree k' t)
    /\ (in_tree k' tr -> in_tree k' t)
    /\ (in_context k' c -> in_tree k' t).
  Proof.
    intros c ; induction c ; intros ; simpl in *
    ; repeat
        match goal with
        | [ |- and (in_tree _ _)  _ ] => constructor ; eauto
        | [ t := Two_t _ _ _ |- _ ] => unfold t
        | [ t := zip _ _ |- _ ] => unfold t
        | [ t := insert_up _ _ |- _ ] => unfold t
        | _ => mysimp
        end ; eauto
    ; repeat
        match goal with
        | [ |- and _ _ ] => constructor
        | [ IH : forall tl k v tr k', and _ (and _ (and _ _))
          |- in_tree ?k (insert_up (?tl,?p,?tr) ?c)
          ] =>
            match p with
            | (?km,?vm) => specialize (IH tl km vm tr)
            | _ => destruct p as [km vm] ; specialize (IH tl km vm tr)
            end ;
            match goal with
            | [ |- in_tree k ?c ] =>
                match c with context [ k ] => specialize (IH k) end
             | [ H : k ~= ?k' |- in_tree k ?c ] =>
                 match c with context [ k' ] => specialize (IH k') end
             | [ H : ?k' ~= k |- in_tree k ?c ] =>
                 match c with context [ k' ] => specialize (IH k') end
            | [ H : in_tree k _ |- _ ] => specialize (IH k)
            | [ H : in_context k _ |- _ ] => specialize (IH k)
            end
        | [ H : in_context ?k (TwoLeftHole_c _ _ _) |- in_tree ?k _ ] =>
            inversion H ; subst ; clear H
        | [ H : in_context ?k (TwoRightHole_c _ _ _) |- in_tree ?k _ ] =>
            inversion H ; subst ; clear H
        | [ H : in_context ?k (ThreeLeftHole_c _ _ _ _ _) |- in_tree ?k _ ] =>
            inversion H ; subst ; clear H
        | [ H : in_context ?k (ThreeMiddleHole_c _ _ _ _ _) |- in_tree ?k _ ] =>
            inversion H ; subst ; clear H
        | [ H : in_context ?k (ThreeRightHole_c _ _ _ _ _) |- in_tree ?k _ ] =>
            inversion H ; subst ; clear H
        | [ Heqv : ?k1 ~= ?k2 , H : _ -> in_tree ?k2 ?t |- in_tree ?k1 ?t ] =>
            eapply (in_tree_Proper k2 k1 (symmetry Heqv) _ _ eq_refl) ; auto
        | [ H : ?x ~= ?x -> _ |- _ ] => specialize (H (reflexivity x))
        | _ => mysimp
        end ; eauto.
  Qed.

  Lemma insert_up_wf :
    forall
      c tl k v tr
      h_lower h_upper h_height c_lower c_upper c_height tl_upper tr_lower,
    context_iwf h_lower h_upper h_height c_lower c_upper c_height c
    -> tree_iwf h_lower tl_upper h_height tl
    -> tl_upper <= Extend k <= tr_lower
    -> tree_iwf tr_lower h_upper h_height tr
    -> exists c_height',
       tree_iwf c_lower c_upper c_height' (insert_up (tl,(k,v),tr) c).
  Proof.
    intros c ; induction c ; intros ; simpl in * ; eauto ; repeat rip ; eauto.
  Qed.

  Lemma remove_up_in :
    forall c t,
    match remove_up t c with
    | None => True
    | Some t' =>
        forall k,
        (in_tree k t -> in_tree k t')
        /\ (in_context k c -> in_tree k t')
    end.
  Proof.
    intros c ; induction c ; intros ; simpl in * ; intros
    ; repeat
        ((repeat
          match goal with
          | [ |- and _ _ ] => constructor
          | [ |- match (match ?t with _ => _ end) with _ => _ end ] => destruct t
          | [ IH : forall t, match remove_up t ?c with _ => _ end
            |- match remove_up ?t ?c with _ => _ end
            ] => specialize (IH t) ; remember (remove_up t c) as m ; destruct m
          | [ H : forall k, and _ _ |- in_tree ?k _ ] => specialize (H k)
          | _ => mysimp
          end ; eauto)
         ; rip).
  Qed.

  Lemma remove_up_in_tree :
    forall c t,
    match remove_up t c with
    | None => True
    | Some t' =>
        forall k, in_tree k t -> in_tree k t'
    end.
  Proof.
    intros.
    remember (remove_up t c) as m.
    pose (remove_up_in c t).
    rewrite <- Heqm in y.
    destruct m ; auto.
    apply y.
  Qed.

  Lemma remove_up_in_context :
    forall c t,
    match remove_up t c with
    | None => True
    | 

  Lemma remove_up_wf :
    forall
      c t
      h_lower h_upper h_height c_lower c_upper c_height,
    context_iwf h_lower h_upper (h_height+1) c_lower c_upper c_height c
    -> tree_iwf h_lower h_upper h_height t
    -> match remove_up t c with
       | None => True
       | Some t' =>
           exists h_height',
           tree_iwf c_lower c_upper h_height' t'
       end.
  Proof.
    Ltac TwoWF_lower_upper tlr trl :=
       match goal with
       | [ H1 : tree_iwf _ ?tl_upper _ tlr
         , H2 : tree_iwf ?tr_lower _ _ trl
         |- _ ] => apply (TwoWF (tl_upper_bound:=tl_upper) (tr_lower_bound:=tr_lower))
       end.
    Ltac TwoWF_dispatch_tr tlr tr :=
      match tr with
      | Two_t ?trl _ _ => TwoWF_lower_upper tlr trl
      | Three_t ?trl _ _ _ _ => TwoWF_lower_upper tlr trl
      | ?trl => TwoWF_lower_upper tlr trl
      end.
    Ltac TwoWF_dispatch tl tr :=
      match tl with
      | Two_t _ _ ?tlr => TwoWF_dispatch_tr tlr tr
      | Three_t _ _ _ _ ?tlr => TwoWF_dispatch_tr tlr tr
      | ?tlr => TwoWF_dispatch_tr tlr tr
      end.
    Ltac ThreeWF_lower_upper tlr tml tmr trl :=
       match goal with
       | [ H1 : tree_iwf _ ?tl_upper _ tlr
         , H2 : tree_iwf ?tml_lower _ _ tml
         , H3 : tree_iwf _ ?tmr_upper _ tmr
         , H4 : tree_iwf ?tr_lower _ _ trl
         |- _ ] => apply (ThreeWF (tl_upper_bound:=tl_upper)
                                  (tm_lower_bound:=tml_lower)
                                  (tm_upper_bound:=tmr_upper)
                                  (tr_lower_bound:=tr_lower))
       end.
    Ltac ThreeWF_dispatch_tr tlr tml tmr tr :=
      match tr with
      | Two_t ?trl _ _ => ThreeWF_lower_upper tlr tml tmr trl
      | Three_t ?trl _ _ _ _ => ThreeWF_lower_upper tlr tml tmr trl
      | ?trl => ThreeWF_lower_upper tlr tml tmr trl
      end.
    Ltac ThreeWF_dispatch_tm tlr tm tr :=
      match tm with
      | Two_t ?tml _ ?tmr => ThreeWF_dispatch_tr tlr tml tmr tr
      | Three_t ?tml _ _ _ ?tmr => ThreeWF_dispatch_tr tlr tml tmr tr
      | ?tm => ThreeWF_dispatch_tr tlr tm tm tr
      end.
    Ltac ThreeWF_dispatch tl tm tr :=
      match tl with
      | Two_t _ _ ?tlr => ThreeWF_dispatch_tm tlr tm tr
      | Three_t _ _ _ _ ?tlr => ThreeWF_dispatch_tm tlr tm tr
      | ?tlr => ThreeWF_dispatch_tm tlr tm tr
      end.
    intros c ; induction c ; intros ; simpl in * ; intros ; repeat rip
    ; repeat
         match goal with
         | [ H : context_iwf _ _ _ _ _ _ Top_c |- _ ] => inversion H ; subst ; clear H
         | [ |- match (match ?t with _ => _ end) with _ => _ end ] => destruct t
         | [ IH : forall t h_lower h_upper h_height c_lower c_upper c_height, _
           , H : context_iwf ?h_lower ?h_upper (?h_height+1) ?c_lower ?c_upper ?c_height _
           |- match remove_up ?t ?c with _ => _ end
           ] => specialize (IHc t h_lower h_upper h_height c_lower c_upper c_height)
                ; remember (remove_up t c) as m ; destruct m
         | [ IH : _ -> _ -> ?G |- ?G ] => apply IH
         | [ H : ?x + ?z = ?y + ?z |- _ ] => apply (proj1 (BinNat.N.add_cancel_r x y z)) in H ; subst
         | [ H : context_iwf _ _ _ _ _ ?c_height ?c
           |- exists h_height, tree_iwf _ _ h_height (zip _ ?c)
           ] => exists c_height
         | [ H : context_iwf _ _ _ ?c_lower ?c_upper ?c_height _
           |- tree_iwf ?c_lower ?c_upper ?c_height (zip _ _)
           ] => refine (zip_wf _ H)
         | [ |- tree_iwf _ _ _ (Two_t ?tl _ ?tr) ] => TwoWF_dispatch tl tr
         | [ |- tree_iwf _ _ _ (Three_t ?tl _ ?tm _ ?tr) ]  => ThreeWF_dispatch tl tm tr
         | _ => mysimp
         end
         ; eauto.
  Qed.

  Lemma remove_in :
    forall t k t_lower t_upper t_height,
    tree_iwf t_lower t_upper t_height t
    -> match remove k t with
       | None => True
       | Some (t',_) =>
         forall k', k' /~= k -> in_tree k' t -> in_tree k' t'
       end.
  Proof.
    intros t ; induction t ; simpl ; intros ; auto.
    - unfold remove ; simpl.
      destruct p.
      remember (k <=>! k0) as m eqn:meqn
      ; symmetry in meqn ; destruct m
      ; [ apply tord_dec_correct_eqv in meqn
        | apply tord_dec_correct_lt in meqn
        | apply tord_dec_correct_gt in meqn
        ].
      + remember (locate_greatest t1 Top_c) as m ; destruct m ; simpl.
        { destruct p.
          destruct s.
          - destruct t2 ; simpl ; auto.
            + remember (remove_up (Three_t Null_t p t2_1 p0 t2_2) (fuse c Top_c)) as m ; destruct m ; simpl ; intros.
              { pose (remove_up_in_tree (fuse c Top_c) (Three_t Null_t p t2_1 p0 t2_2)).
                rewrite <- Heqm0 in y.
                apply y.
                pose (locate_greatest_in t1 Top_c).
                rewrite <- Heqm in y0 ; destruct p ; simpl in y0.
                pose (locate_greatest_in_result t1 Top_c).
                rewrite <- Heqm in y1.
                specialize (y0 k).
                inversion H1 ; subst ; clear H1.
                - specialize (y0 k).
    
  Lemma remove_spec :
    forall k t t_lower t_upper t_height,
    tree_iwf t_lower t_upper t_height t
    -> match remove k t with
       | None => True
       | Some (t',vM) =>
           ~ in_tree k t'
           /\ (forall k', k' /~= k -> in_tree k' t -> in_tree k' t')
           /\ match vM with
              | None => ~ in_tree k t
              | Some v => in_tree k t /\ lookup k t = Some v
              end
           /\
       end.
            
      
           
  Program Definition empty_wf : with_wf (tree K V) := exist _ empty _.
  Next Obligation.
    exists 0, (lbot:extend K) , (lbot:extend K) ; constructor ; reflexivity.
  Defined.

  Program Definition singleton_wf (k:K) (v:V) : with_wf (tree K V) := exist _ (singleton k v) _.
  Next Obligation.
    exists (0+1), (lbot:extend K), (ltop:extend K).
    econstructor ; eauto ; constructor ; [ apply lbot_ineq | apply ltop_ineq ].
  Defined.

  Definition tree_inwf (k:K) (twf:with_wf (tree K V)) : Prop := in_tree k (proj1_sig twf).

  Definition lookup_wf (k:K) (twf:with_wf (tree K V)) `(! tree_inwf k twf ) : V.
  Proof.
    destruct twf as [t p].
    elimtype { v | lookup k t = Some v} ; intros.
    { exact x. }
    unfold lookup ; unfold tree_inwf in tree_inwf0 ; simpl in tree_inwf0
    ; remember (locate k t Top_c) as m ; destruct m
    ; pose (locate_in t k Top_c) ; rewrite <- Heqm in y ; repeat mysimp.
    - exfalso.
      destruct p as [n Ex] ; destruct Ex as [kM Ex] ; destruct Ex.
      pose (locate_not_in k Top_c H).
      rewrite <- Heqm in y0.
      contradiction.
    - econstructor ; reflexivity.
  Qed.

  
  
End TwoThreeTreesWF.