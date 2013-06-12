Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Classes.
Require Import FP.Data.Sum.
Require Import FP.Data.Prod.
Require Import FP.Data.Option.
Require Import FP.Data.Extend.
Require Import FP.Data.TwoThreeTrees.

Import CoreClassesNotation.
Import CoreDataNotation.
Import ClassesNotation.


Module TwoThreeTreesWF.
  Import TwoThreeTrees.

  Section Context.
    Context {K V:Type}
      `{! Lte K ,! Eqv K ,! ER_WF K ,! TotalOrd K
       ,! TotalOrdDec K ,! TotalOrd_RDC K
       ,! EqvDec K ,! Eqv_RDC K
       }.

    Inductive empty_tree : tree K V -> Prop :=
      | Empty_Null : empty_tree Null_t.
    Hint Constructors empty_tree.

    Inductive not_empty_tree : tree K V -> Prop :=
      | NotEmpty_Two : forall tl p tr, not_empty_tree (Two_t tl p tr)
      | NotEmtpy_Three : forall tl pl tm pr tr, not_empty_tree (Three_t tl pl tm pr tr).
    Hint Constructors not_empty_tree.
    
    Inductive in_tree : K -> tree K V -> Prop :=
      | In_TwoLeftTree :
          forall k tl pm tr, in_tree k tl -> in_tree k (Two_t tl pm tr)
      | In_TwoNode :
          forall k k' v tl tr, k ~= k' -> in_tree k (Two_t tl (k',v) tr)
      | In_TwoRightTree :
          forall k tl pm tr, in_tree k tr -> in_tree k (Two_t tl pm tr)
      | In_ThreeLeftTree :
          forall k tl pl tm pr tr, in_tree k tl -> in_tree k (Three_t tl pl tm pr tr)
      | In_ThreeLeftNode :
          forall k k' v tl tm pr tr, k ~= k' -> in_tree k (Three_t tl (k',v) tm pr tr)
      | In_ThreeMiddleTree :
          forall k tl pl tm pr tr, in_tree k tm -> in_tree k (Three_t tl pl tm pr tr)
      | In_ThreeRightNode :
          forall k k' v tl pl tm tr, k ~= k' -> in_tree k (Three_t tl pl tm (k',v) tr)
      | In_ThreeRightTree :
          forall k tl pl tm pr tr, in_tree k tr -> in_tree k (Three_t tl pl tm pr tr).
    Hint Constructors in_tree.

    Inductive maps_tree : K -> V -> tree K V -> Prop :=
      | Maps_TwoLeftTree :
          forall k v tl pm tr, maps_tree k v tl -> maps_tree k v (Two_t tl pm tr)
      | Maps_TwoNode :
          forall k k' v tl tr, k ~= k' -> maps_tree k v (Two_t tl (k',v) tr)
      | Maps_TwoRightTree :
          forall k v tl pm tr, maps_tree k v tr -> maps_tree k v (Two_t tl pm tr)
      | Maps_ThreeLeftTree :
          forall k v tl pl tm pr tr, maps_tree k v tl -> maps_tree k v (Three_t tl pl tm pr tr)
      | Maps_ThreeLeftNode :
          forall k k' v tl tm pr tr, k ~= k' -> maps_tree k v (Three_t tl (k',v) tm pr tr)
      | Maps_ThreeMiddleTree :
          forall k v tl pl tm pr tr, maps_tree k v tm -> maps_tree k v (Three_t tl pl tm pr tr)
      | Maps_ThreeRightNode :
          forall k k' v tl pl tm tr, k ~= k' -> maps_tree k v (Three_t tl pl tm (k',v) tr)
      | Maps_ThreeRightTree :
          forall k v tl pl tm pr tr, maps_tree k v tr -> maps_tree k v (Three_t tl pl tm pr tr).
    Hint Constructors maps_tree.

    Inductive not_in_tree : K -> tree K V -> Prop :=
      | NotIn_Null : forall k, not_in_tree k Null_t
      | NotIn_Two :
          forall k tl km vm tr,
          not_in_tree k tl
          -> k /~= km -> not_in_tree k tr
          -> not_in_tree k (Two_t tl (km,vm) tr)
      | NotIn_Three :
          forall k tl kl vl tm kr vr tr,
          not_in_tree k tl
          -> k /~= kl -> not_in_tree k tm
          -> k /~= kr -> not_in_tree k tr
          -> not_in_tree k (Three_t tl (kl,vl) tm (kr,vr) tr).
    Hint Constructors not_in_tree.

    Inductive bst_tree : extend K -> extend K -> tree K V -> Prop :=
      | BST_Null : forall l u, l <= u -> bst_tree l u Null_t
      | BST_Two :
          forall l_tl tl k v u_tr tr,
          bst_tree l_tl (Extend k) tl
          -> bst_tree (Extend k) u_tr tr
          -> bst_tree l_tl u_tr (Two_t tl (k,v) tr)
      | BST_Three :
          forall l_tl tl kl vl tm kr vr u_tr tr,
          bst_tree l_tl (Extend kl) tl
          -> bst_tree (Extend kl) (Extend kr) tm
          -> bst_tree (Extend kr) u_tr tr
          -> bst_tree l_tl u_tr (Three_t tl (kl,vl) tm (kr,vr) tr).
    Hint Constructors bst_tree.

    Inductive balance_tree : N -> tree K V -> Prop :=
      | Balance_Null : balance_tree 0 Null_t
      | Balance_Two :
          forall n tl p tr,
          balance_tree n tl
          -> balance_tree n tr
          -> balance_tree (n+1) (Two_t tl p tr)
      | Balance_Three :
          forall n tl pl tm pr tr,
          balance_tree n tl
          -> balance_tree n tm
          -> balance_tree n tr
          -> balance_tree (n+1) (Three_t tl pl tm pr tr).
    Hint Constructors balance_tree.

    Inductive in_context : K -> context K V -> Prop :=
      | In_TwoLeftHoleNode :
          forall k k' v tr c, k ~= k' -> in_context k (TwoLeftHole_c (k',v) tr c)
      | In_TwoLeftHoleTree :
          forall k pm tr c, in_tree k tr -> in_context k (TwoLeftHole_c pm tr c)
      | In_TwoLeftHoleContext :
          forall k pm tr c, in_context k c -> in_context k (TwoLeftHole_c pm tr c)
      | In_TwoRightHoleTree :
          forall k tl pm c, in_tree k tl -> in_context k (TwoRightHole_c tl pm c)
      | In_TwoRightHoleNode :
          forall k k' v tl c, k ~= k' -> in_context k (TwoRightHole_c tl (k',v) c)
      | In_TwoRightHoleContext :
          forall k tl pm c, in_context k c -> in_context k (TwoRightHole_c tl pm c)
      | In_ThreeLeftHoleLeftNode :
          forall k k' v tm pr tr c, k ~= k' -> in_context k (ThreeLeftHole_c (k',v) tm pr tr c)
      | In_ThreeLeftHoleMiddleTree :
          forall k pl tm pr tr c, in_tree k tm -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | In_ThreeLeftHoleRightNode :
          forall k k' v pl tm tr c, k ~= k' -> in_context k (ThreeLeftHole_c pl tm (k',v) tr c)
      | In_ThreeLeftHoleRightTree :
          forall k pl tm pr tr c, in_tree k tr -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | In_ThreeLeftHoleContext :
          forall k pl tm pr tr c, in_context k c -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | In_ThreeMiddleHoleLeftTree :
          forall k tl pl pr tr c, in_tree k tl -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | In_ThreeMiddleHoleLeftNode :
          forall k k' v tl pr tr c, k ~= k' -> in_context k (ThreeMiddleHole_c tl (k',v) pr tr c)
      | In_ThreeMiddleHoleRightNode :
          forall k k' v tl pl tr c, k ~= k' -> in_context k (ThreeMiddleHole_c tl pl (k',v) tr c)
      | In_ThreeMiddleHoleRightTree :
          forall k tl pl pr tr c, in_tree k tr -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | In_ThreeMiddleHoleContext :
          forall k tl pl pr tr c, in_context k c -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | In_ThreeRightHoleLeftTree :
          forall k tl pl tm pr c, in_tree k tl -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | In_ThreeRightHoleLeftNode :
          forall k k' v tl tm pr c, k ~= k' -> in_context k (ThreeRightHole_c tl (k',v) tm pr c)
      | In_ThreeRightHoleMiddleTree :
          forall k tl pl tm pr c, in_tree k tm -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | In_ThreeRightHoleRightNode :
          forall k v tl pl tm c, in_context k (ThreeRightHole_c tl pl tm (k,v) c)
      | In_ThreeRightHoleContext :
          forall k tl pl tm pr c, in_context k c -> in_context k (ThreeRightHole_c tl pl tm pr c).
    Hint Constructors in_context.

    Inductive not_in_context : K -> context K V -> Prop :=
      | NotIn_Top : forall k, not_in_context k Top_c
      | NotIn_TwoLeftHole :
          forall k km vm tr c,
          k /~= km -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_context k (TwoLeftHole_c (km,vm) tr c)
      | NotIn_TwoRightHole :
          forall k tl km vm c,
          not_in_tree k tl
          -> k /~= km -> not_in_context k c
          -> not_in_context k (TwoRightHole_c tl (km,vm) c)
      | NotIn_ThreeLeftHole :
          forall k kl vl tm kr vr tr c,
          k /~= kl -> not_in_tree k tm
          -> k /~= kr -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_context k (ThreeLeftHole_c (kl,vl) tm (kr,vr) tr c)
      | NotIn_ThreeMiddleHole :
          forall k tl kl vl kr vr tr c,
          not_in_tree k tl
          -> k /~= kl
          -> k /~= kr -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_context k (ThreeMiddleHole_c tl (kl,vl) (kr,vr) tr c)
      | NotIn_ThreeRightHole :
          forall k tl kl vl tm kr vr c,
          not_in_tree k tl
          -> k /~= kl -> not_in_tree k tm
          -> k /~= kr -> not_in_context k c
          -> not_in_context k (ThreeRightHole_c tl (kl,vl) tm (kr,vr) c).
    Hint Constructors not_in_context.

    Inductive maps_context : K -> V -> context K V -> Prop :=
      | Maps_TwoLeftHoleNode :
          forall k k' v tr c, k ~= k' -> maps_context k v (TwoLeftHole_c (k',v) tr c)
      | Maps_TwoLeftHoleTree :
          forall k v pm tr c, maps_tree k v tr -> maps_context k v (TwoLeftHole_c pm tr c)
      | Maps_TwoLeftHoleContext :
          forall k v pm tr c, maps_context k v c -> maps_context k v (TwoLeftHole_c pm tr c)
      | Maps_TwoRightHoleTree :
          forall k v tl pm c, maps_tree k v tl -> maps_context k v (TwoRightHole_c tl pm c)
      | Maps_TwoRightHoleNode :
          forall k k' v tl c, k ~= k' -> maps_context k v (TwoRightHole_c tl (k',v) c)
      | Maps_TwoRightHoleContext :
          forall k v tl pm c, maps_context k v c -> maps_context k v (TwoRightHole_c tl pm c)
      | Maps_ThreeLeftHoleLeftNode :
          forall k k' v tm pr tr c, k ~= k' -> maps_context k v (ThreeLeftHole_c (k',v) tm pr tr c)
      | Maps_ThreeLeftHoleMiddleTree :
          forall k v pl tm pr tr c, maps_tree k v tm -> maps_context k v (ThreeLeftHole_c pl tm pr tr c)
      | Maps_ThreeLeftHoleRightNode :
          forall k k' v pl tm tr c, k ~= k' -> maps_context k v (ThreeLeftHole_c pl tm (k',v) tr c)
      | Maps_ThreeLeftHoleRightTree :
          forall k v pl tm pr tr c, maps_tree k v tr -> maps_context k v (ThreeLeftHole_c pl tm pr tr c)
      | Maps_ThreeLeftHoleContext :
          forall k v pl tm pr tr c, maps_context k v c -> maps_context k v (ThreeLeftHole_c pl tm pr tr c)
      | Maps_ThreeMiddleHoleLeftTree :
          forall k v tl pl pr tr c, maps_tree k v tl -> maps_context k v (ThreeMiddleHole_c tl pl pr tr c)
      | Maps_ThreeMiddleHoleLeftNode :
          forall k k' v tl pr tr c, k ~= k' -> maps_context k v (ThreeMiddleHole_c tl (k',v) pr tr c)
      | Maps_ThreeMiddleHoleRightNode :
          forall k k' v tl pl tr c, k ~= k' -> maps_context k v (ThreeMiddleHole_c tl pl (k',v) tr c)
      | Maps_ThreeMiddleHoleRightTree :
          forall k v tl pl pr tr c, maps_tree k v tr -> maps_context k v (ThreeMiddleHole_c tl pl pr tr c)
      | Maps_ThreeMiddleHoleContext :
          forall k v tl pl pr tr c, maps_context k v c -> maps_context k v (ThreeMiddleHole_c tl pl pr tr c)
      | Maps_ThreeRightHoleLeftTree :
          forall k v tl pl tm pr c, maps_tree k v tl -> maps_context k v (ThreeRightHole_c tl pl tm pr c)
      | Maps_ThreeRightHoleLeftNode :
          forall k k' v tl tm pr c, k ~= k' -> maps_context k v (ThreeRightHole_c tl (k',v) tm pr c)
      | Maps_ThreeRightHoleMiddleTree :
          forall k v tl pl tm pr c, maps_tree k v tm -> maps_context k v (ThreeRightHole_c tl pl tm pr c)
      | Maps_ThreeRightHoleRightNode :
          forall k v tl pl tm c, maps_context k v (ThreeRightHole_c tl pl tm (k,v) c)
      | Maps_ThreeRightHoleContext :
          forall k v tl pl tm pr c, maps_context k v c -> maps_context k v (ThreeRightHole_c tl pl tm pr c).
    Hint Constructors maps_context.

    Inductive bst_context l_r u_r : extend K -> extend K -> context K V -> Prop :=
      | BST_Top : bst_context l_r u_r l_r u_r Top_c
      | BST_TwoLeftHole :
          forall l_c u_tr km vm tr c,
          bst_tree (Extend km) u_tr tr
          -> bst_context l_r u_r l_c u_tr c
          -> bst_context l_r u_r l_c (Extend km) (TwoLeftHole_c (km,vm) tr c)
      | BST_TwoRightHole :
          forall l_tl u_c tl km vm c,
          bst_tree l_tl (Extend km) tl
          -> bst_context l_r u_r l_tl u_c c
          -> bst_context l_r u_r (Extend km) u_c (TwoRightHole_c tl (km,vm) c)
      | BST_ThreeLeftHole :
          forall l_c u_tr kl vl tm kr vr tr c,
          bst_tree (Extend kl) (Extend kr) tm
          -> bst_tree (Extend kr) u_tr tr
          -> bst_context l_r u_r l_c u_tr c
          -> bst_context l_r u_r l_c (Extend kl) (ThreeLeftHole_c (kl,vl) tm (kr,vr) tr c)
      | BST_ThreeMiddleHole :
          forall l_tl u_tr tl kl vl kr vr tr c,
          bst_tree l_tl (Extend kl) tl
          -> bst_tree (Extend kr) u_tr tr
          -> bst_context l_r u_r l_tl u_tr c
          -> bst_context l_r u_r (Extend kl) (Extend kr) (ThreeMiddleHole_c tl (kl,vl) (kr,vr) tr c)
      | BST_ThreeRightHole :
          forall l_tl u_c tl kl vl tm kr vr c,
          bst_tree l_tl (Extend kl) tl
          -> bst_tree (Extend kl) (Extend kr) tm
          -> bst_context l_r u_r l_tl u_c c
          -> bst_context l_r u_r (Extend kr) u_c (ThreeRightHole_c tl (kl,vl) tm (kr,vr) c).
    Hint Constructors bst_context.

    Inductive balance_context : N -> N -> context K V -> Prop :=
      | Balance_Top : forall n, balance_context n n Top_c
      | Balance_TwoLeftHole :
          forall n n' pm tr c,
          balance_tree n tr
          -> balance_context (n+1) n' c
          -> balance_context n n' (TwoLeftHole_c pm tr c)
     | Balance_TwoRightHole :
         forall n n' tl pm c,
         balance_tree n tl
         -> balance_context (n+1) n' c
         -> balance_context n n' (TwoRightHole_c tl pm c)
     | Balance_ThreeLeftHole :
         forall n n' pl tm pr tr c,
         balance_tree n tm
         -> balance_tree n tr
         -> balance_context (n+1) n' c
         -> balance_context n n' (ThreeLeftHole_c pl tm pr tr c)
     | Balance_ThreeMiddleHole :
         forall n n' tl pl pr tr c,
         balance_tree n tl
         -> balance_tree n tr
         -> balance_context (n+1) n' c
         -> balance_context n n' (ThreeMiddleHole_c tl pl pr tr c)
     | Balance_ThreeRightHole :
         forall n n' tl pl tm pr c,
         balance_tree n tl
         -> balance_tree n tm
         -> balance_context (n+1) n' c
         -> balance_context n n' (ThreeRightHole_c tl pl tm pr c).
    Hint Constructors balance_context.

    Inductive in_location : K -> location K V -> Prop :=
      | In_LocTwoHoleLeftTree :
          forall k tl tr c, in_tree k tl -> in_location k (TwoHole_l tl tr c)
      | In_LocTwoHoleRightTree :
          forall k tl tr c, in_tree k tr -> in_location k (TwoHole_l tl tr c)
      | In_LocTwoHoleContext :
          forall k tl tr c, in_context k c -> in_location k (TwoHole_l tl tr c)
      | In_LocThreeLeftHoleLeftTree :
          forall k tl tm pr tr c, in_tree k tl -> in_location k (ThreeLeftHole_l tl tm pr tr c)
      | In_LocThreeLeftHoleMiddleTree :
          forall k tl tm pr tr c, in_tree k tm -> in_location k (ThreeLeftHole_l tl tm pr tr c)
      | In_LocThreeLeftHoleNode :
          forall k k' v tl tm tr c, k ~= k' -> in_location k (ThreeLeftHole_l tl tm (k',v) tr c)
      | In_LocThreeLeftHoleRightTree :
          forall k tl tm pr tr c, in_tree k tr -> in_location k (ThreeLeftHole_l tl tm pr tr c)
      | In_LocThreeLeftHoleContext :
          forall k tl tm pr tr c, in_context k c -> in_location k (ThreeLeftHole_l tl tm pr tr c)
      | In_LocThreeRightHoleLeftTree :
          forall k tl pl tm tr c, in_tree k tl -> in_location k (ThreeRightHole_l tl pl tm tr c)
      | In_LocThreeRightHoleNode :
          forall k k' v tl tm tr c, k ~= k' -> in_location k (ThreeRightHole_l tl (k',v) tm tr c)
      | In_LocThreeRightHoleMiddleTree :
          forall k tl pl tm tr c, in_tree k tm -> in_location k (ThreeRightHole_l tl pl tm tr c)
      | In_LocThreeRightHoleRightTree :
          forall k tl pl tm tr c, in_tree k tr -> in_location k (ThreeRightHole_l tl pl tm tr c)
      | In_LocThreeRightHoleContext :
          forall k tl pl tm tr c, in_context k c -> in_location k (ThreeRightHole_l tl pl tm tr c).
    Hint Constructors in_location.

    Inductive maps_location : K -> V -> location K V -> Prop :=
      | Maps_LocTwoHoleLeftTree :
          forall k v tl tr c, maps_tree k v tl -> maps_location k v (TwoHole_l tl tr c)
      | Maps_LocTwoHoleRightTree :
          forall k v tl tr c, maps_tree k v tr -> maps_location k v (TwoHole_l tl tr c)
      | Maps_LocTwoHoleContext :
          forall k v tl tr c, maps_context k v c -> maps_location k v (TwoHole_l tl tr c)
      | Maps_LocThreeLeftHoleLeftTree :
          forall k v tl tm pr tr c, maps_tree k v tl -> maps_location k v (ThreeLeftHole_l tl tm pr tr c)
      | Maps_LocThreeLeftHoleMiddleTree :
          forall k v tl tm pr tr c, maps_tree k v tm -> maps_location k v (ThreeLeftHole_l tl tm pr tr c)
      | Maps_LocThreeLeftHoleNode :
          forall k k' v tl tm tr c, k ~= k' -> maps_location k v (ThreeLeftHole_l tl tm (k',v) tr c)
      | Maps_LocThreeLeftHoleRightTree :
          forall k v tl tm pr tr c, maps_tree k v tr -> maps_location k v (ThreeLeftHole_l tl tm pr tr c)
      | Maps_LocThreeLeftHoleContext :
          forall k v tl tm pr tr c, maps_context k v c -> maps_location k v (ThreeLeftHole_l tl tm pr tr c)
      | Maps_LocThreeRightHoleLeftTree :
          forall k v tl pl tm tr c, maps_tree k v tl -> maps_location k v (ThreeRightHole_l tl pl tm tr c)
      | Maps_LocThreeRightHoleNode :
          forall k k' v tl tm tr c, k ~= k' -> maps_location k v (ThreeRightHole_l tl (k',v) tm tr c)
      | Maps_LocThreeRightHoleMiddleTree :
          forall k v tl pl tm tr c, maps_tree k v tm -> maps_location k v (ThreeRightHole_l tl pl tm tr c)
      | Maps_LocThreeRightHoleRightTree :
          forall k v tl pl tm tr c, maps_tree k v tr -> maps_location k v (ThreeRightHole_l tl pl tm tr c)
      | Maps_LocThreeRightHoleContext :
          forall k v tl pl tm tr c, maps_context k v c -> maps_location k v (ThreeRightHole_l tl pl tm tr c).
    Hint Constructors maps_location.

    Inductive not_in_location : K -> location K V -> Prop :=
      | NotIn_TwoNode :
          forall k tl tr c,
          not_in_tree k tl
          -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_location k (TwoHole_l tl tr c)
      | NotIn_ThreeLeftNode :
          forall k tl tm kr vr tr c,
          not_in_tree k tl
          -> not_in_tree k tm
          -> k /~= kr -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_location k (ThreeLeftHole_l tl tm (kr,vr) tr c)
      | NotIn_ThreeRightNode :                   
          forall k tl kl vl tm tr c,
          not_in_tree k tl
          -> k /~= kl -> not_in_tree k tm
          -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_location k (ThreeRightHole_l tl (kl,vl) tm  tr c).
    Hint Constructors not_in_location.

    Inductive bst_location l_r u_r : extend K -> location K V -> Prop :=
      | BST_TwoHole :
          forall kM l_c u_c tl tr c,
          bst_tree l_c kM tl
          -> bst_tree kM u_c tr
          -> bst_context l_r u_r l_c u_c c
          -> bst_location l_r u_r kM (TwoHole_l tl tr c)
      | BST_ThreeLeftNodeHole :
          forall kM l_c u_c tl tm kr vr tr c,
          bst_tree l_c kM tl
          -> bst_tree kM (Extend kr) tm
          -> bst_tree (Extend kr) u_c tr
          -> bst_context l_r u_r l_c u_c c
          -> bst_location l_r u_r kM (ThreeLeftHole_l tl tm (kr,vr) tr c)
      | BST_ThreeRightNodeHole :
          forall kM l_c u_c tl kl vl tm tr c,
          bst_tree l_c (Extend kl) tl
          -> bst_tree (Extend kl) kM tm
          -> bst_tree kM u_c tr
          -> bst_context l_r u_r l_c u_c c
          -> bst_location l_r u_r kM (ThreeRightHole_l tl (kl,vl) tm tr c).
    Hint Constructors bst_location.

    Inductive balance_location : N -> location K V -> Prop :=
      | Balance_TwoHole :
          forall n tl tr n' c,
          balance_tree n tl
          -> balance_tree n tr
          -> balance_context (n+1) n' c
          -> balance_location n' (TwoHole_l tl tr c)
      | Balance_ThreeLeftNodeHole :
          forall n tl tm pr tr n' c,
          balance_tree n tl
          -> balance_tree n tm
          -> balance_tree n tr
          -> balance_context (n+1) n' c
          -> balance_location n' (ThreeLeftHole_l tl tm pr tr c)
      | Balance_ThreeRightNodeHole :
          forall n tl pl tm tr n' c,
          balance_tree n tl
          -> balance_tree n tm
          -> balance_tree n tr
          -> balance_context (n+1) n' c
          -> balance_location n' (ThreeRightHole_l tl pl tm tr c).

    Local Ltac gd x := generalize dependent x.

    Lemma plus_one_elim : forall {x y}, x+1 = y+1 -> x=y.
    Proof.
      intros.
      assert (1+x=y+1).
      { transitivity (x+1) ; auto.
        symmetry.
        apply (BinNat.N.add_comm x 1).
      }
      assert (1+x=1+y).
      { transitivity (y+1) ; auto.
        apply (BinNat.N.add_comm y 1).
      }
      exact (BinNat.Nplus_reg_l 1 x y H1).
    Qed.
    Hint Immediate plus_one_elim.

    Lemma plus_one_not_zero_l : forall {n}, 0 = n+1 -> False.
    Admitted.
    (*
    Proof.
      intros n Heq ; destruct n ; unfold "+" in * ; simpl in * ; discriminate Heq.
    Qed.
    *)

    Lemma plus_one_not_zero_r : forall {n}, n+1 = 0 -> False.
    Admitted.
    (*
    Proof.
      intros n H ; symmetry in H ; eauto.
    Qed.
    *)

    Lemma lt_eqv_contradiction : forall {x y}, x < y -> x /~= y.
    Admitted.
    (*
    Proof.
      intros x y Hlt Heqv ; apply Hlt ; refine (PartialOrd_respect_eqv y y _ y x _ _)
      ; try reflexivity ; symmetry ; auto.
    Qed.
    *)
    Hint Immediate lt_eqv_contradiction.

    Lemma lt_eqv_contradiction' : forall {x y}, x < y -> y /~= x.
    Admitted.
    (*
    Proof.
      intros x y Hlt Heqv ; apply Hlt ; refine (PartialOrd_respect_eqv y y _ y x _ _)
      ; try reflexivity ; auto.
    Qed.
    *)
    Hint Immediate lt_eqv_contradiction'.

    Ltac mysimp := fail.
    Hint Extern 0 => mysimp.

    Ltac mysimp0 :=
      match goal with
      (* basic rules *)
      | [ |- and _ _ ] => constructor
      | [ |- ~ _ ] => unfold "~" at 1 ; intros

      | [ H : and _ _ |- _ ] => destruct H
      | [ H : exists _, _ |- _ ] => destruct H
      | [ H : ?x /\ _ |- _ ] => match type of x with Prop => destruct H | _ => fail end
      | [ H : _ <-> _ |- _ ] => destruct H
      | [ H1 : ?X , H2 : ?X -> exists _, _ |- _ ] => specialize (H2 H1) ; destruct H2
      | [ H : false = _ ~=! _ |- _ ] => symmetry in H ; apply neg_dec_correct in H
      | [ H : true = _ ~=! _ |- _ ] => symmetry in H ; apply dec_correct in H
      | [ H : Lt = _ <=>! _ |- _ ] => symmetry in H ; apply tord_dec_correct_lt in H
      | [ H : Eq = _ <=>! _ |- _ ] => symmetry in H ; apply tord_dec_correct_eqv in H
      | [ H : Gt = _ <=>! _ |- _ ] => symmetry in H ; apply tord_dec_correct_gt in H
      | [ H : ?x+1 = ?y+1 |- _ ] => apply plus_one_elim in H ; subst x
      | [ H : 0 = _ + 1 |- _ ] => exfalso ; apply (plus_one_not_zero_l H)
      | [ H : _ + 1 = 0 |- _ ] => exfalso ; apply (plus_one_not_zero_r H)
      | [ H : None = None |- _ ] => clear H
      | [ H : Some _ = Some _ |- _ ] => injection H ; intros ; subst ; clear H
      | [ H1 : ?X -> ~?Y , H2 : ?X , H3 : ?Y |- _ ] => exfalso ; apply (H1 H2 H3)

      (* tree rules *)
      | [ |- not_in_tree _ (Two_t _ (_,_) _) ] => fail 1
      | [ |- not_in_tree _ (Two_t _ ?p _) ] => destruct p
      | [ |- not_in_tree _ (Three_t _ (_,_) _ (_,_) _) ] => fail 1
      | [ |- not_in_tree _ (Three_t _ ?p _ (_,_) _) ] => destruct p
      | [ |- not_in_tree _ (Three_t _ (_,_) _ ?p _) ] => destruct p
      | [ |- not_in_tree _ (Three_t _ ?pl _ ?pr _) ] => destruct pl,pr

      | [ H : in_tree _ Null_t |- _ ] => inversion H
      | [ H : maps_tree _ _ Null_t |- _ ] => inversion H
      | [ H : in_context _ Top_c |- _ ] => inversion H

      | [ H : empty_tree _ |- _ ] => inversion H ; subst ; clear H
      | [ H : not_in_tree _ Null_t |- _ ] => inversion H ; subst ; clear H
      | [ H : not_in_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : not_in_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_tree _ _ Null_t |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_tree _ _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_tree _ _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_tree _ Null_t |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_tree 0 _ |- _ ] => inversion H ; subst ; clear H ; try mysimp
      | [ H : in_context _ _ _ _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ _ _ _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ _ _ _ (ThreeRightHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ Top_c |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (TwoLeftHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (TwoRightHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (ThreeRightHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ Top_c |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (TwoLeftHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (TwoRightHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (ThreeRightHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_location _ _ _ (TwoHole_l _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_location _ _ _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_location _ _ _ (ThreeRightHole_l _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_location _ (TwoHole_l _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_location _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_location _ (ThreeRightHole_l _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      end.
    Ltac mysimp ::= mysimp0.

    Local Ltac rip :=
      match goal with
      (* basic rules *)
      | [ H : or _ _ |- _ ] => inversion H ; subst ; clear H

      (* tree rules *)
      | [ H : in_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : maps_tree _ _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : maps_tree _ _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (TwoLeftHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (TwoRightHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (ThreeRightHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      end.

    Ltac flip_eqn x :=
      match goal with
      | [ H : _ = ?E |- _ ] => match E with context [ x ] => symmetry in H end
      end.

    Ltac let_pair_drill :=
      match goal with
      | [ |- context [ let (_,_) := ?p in _ ] ] => destruct p
      | [ H : context [ let (_,_) := ?p in _ ] |- _ ] => destruct p
      end.

    Ltac tord_drill :=
      match goal with
      | [ |- context [?x <=>! ?y] ] =>
          let m := fresh "tord" in remember (x <=>! y) as m ; destruct m
      end.

    Ltac atom_match_drill :=
      match goal with
      | [ |- context [ match ?X with _ => _ end ] ] =>
          match X with (?f _) => fail 1 | _ => destruct X end
      | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
          match X with (?f _) => fail 1 | _ => destruct X end
      end.

    Lemma null_bst_lib : forall {m}, bst_tree m m Null_t.
    Admitted.
    (*
    Proof.
      intros ; econstructor ; reflexivity.
    Qed.
    *)
    Hint Immediate null_bst_lib.

    Lemma empty_balance_zero : forall {t}, empty_tree t -> balance_tree 0 t.
    Proof.
      intros t H ; inversion H ; eauto.
    Qed.
    Hint Resolve empty_balance_zero.

    Lemma balance_tree_unique : forall {n n' t}, balance_tree n t -> balance_tree n' t -> n = n'.
    Proof.
      intros n n' t ; gd n' ; gd n ; induction t ; intros ; repeat mysimp || rip ; eauto.
      rewrite (IHt1 _ _ H3 H4) ; auto.
      rewrite (IHt1 _ _ H4 H5) ; auto.
    Qed.
    Ltac balance_tree_unique_zero :=
      match goal with
      | [ Hemp : empty_tree ?t , Hbal : balance_tree ?n ?t |- _ ] =>
          match n with
          | 0 => fail 1
          | _ => assert (n = 0) ; [ eapply (balance_tree_unique Hbal) ; clear Hbal | subst ]
          end
      end.
    Ltac mysimp1 := mysimp0 || balance_tree_unique_zero.
    Ltac mysimp ::= mysimp1.

    Lemma balance_tree_two_right_matches_left :
      forall {n tl tr n' c},
      balance_tree n tl -> balance_location n' (TwoHole_l tl tr c) -> balance_tree n tr.
    Proof.
      intros. inversion H0 ; subst ; clear H0.
      rewrite (balance_tree_unique H H5) ; auto.
    Qed.

    Lemma maps_to_in : forall {k t v}, maps_tree k v t -> in_tree k t.
    Admitted.
    (* 
    Proof.
      intros k t v H ; induction t ; repeat mysimp || rip ; eauto.
    Qed.
    *)
    Hint Resolve maps_to_in.

    Lemma in_to_maps_ex : forall {k t}, in_tree k t -> exists v, maps_tree k v t.
    Admitted.
    (*
    Proof.
      intros k t H ; induction t ; repeat mysimp || rip ; eauto.
    Qed.
    *)

    Lemma not_in_to_neg_in_tree : forall k t, not_in_tree k t <-> ~in_tree k t.
    Admitted.
    (*
    Proof. intros ; induction t ; constructor ; intros ; repeat mysimp || rip ; eauto.  Qed.
    *)

    Lemma in_tree_dp : forall k t, in_tree k t \/ not_in_tree k t.
    Admitted.
    (*
    Proof.
      intros k t ; induction t ; repeat mysimp || rip || auto ; eauto.
      - destruct p as [k' v].
        remember (k <=>! k') as m ; destruct m ; repeat mysimp ; eauto
        ; right ; repeat mysimp || rip || auto ; eauto.
      - destruct p as [k' v], p0 as [k0' v0].
        remember (k <=>! k') as m ; destruct m ; repeat mysimp ; eauto
        ; remember (k <=>! k0') as m ; destruct m ; repeat mysimp ; eauto
        ; right ; repeat mysimp || rip || auto ; eauto.
    Qed.
    *)

    Lemma empty_tree_dp : forall t, empty_tree t \/ not_empty_tree t.
    Proof. intros t ; destruct t ; eauto. Qed.

    Ltac in_tree_case k t :=
      let Hin := fresh "Hin" in
      let Hmaps := fresh "Hmaps" in
      let Hnotin := fresh "Hnotin" in
      let v := fresh "v" in
      destruct (in_tree_dp k t) as [Hin | Hnotin]
      ; [apply in_to_maps_ex in Hin ; destruct Hin as [v Hmaps]|].

    Lemma bst_tree_weaken :
      forall l_t l_t' u_t u_t' t,
      bst_tree l_t u_t t -> l_t' <= l_t -> u_t' >= u_t -> bst_tree l_t' u_t' t.
    Admitted.
    Hint Immediate bst_tree_weaken.

    (* Lemmas about single *)

    (*
    Lemma single_maps :
      forall {k k' v},
      k ~= k'
      -> maps_tree k v (single (k',v)).
    Admitted.
    Hint Resolve single_maps.
             
    Lemma single_not_in :
      forall {k k' v},
      k /~= k'
      -> not_in_tree k (single (k',v)).
    Admitted.
    Hint Resolve single_not_in.
    *)
    
    (* Lemmas about zip *)

    (*
    Lemma zip_maps_intro :
      forall {k v t c},
      maps_tree k v t \/ maps_context k v c
      -> maps_tree k v (zip t c).
    Admitted.
    Hint Resolve zip_maps_intro.

    Lemma zip_maps_elim_t :
      forall {k v t c},
      maps_tree k v (zip t c)
      -> not_in_tree k t
      -> maps_context k v c.
    Admitted.
    Hint Resolve zip_maps_elim_t.

    Lemma zip_maps_elim_c :
      forall {k v t c},
      maps_tree k v (zip t c)
      -> not_in_context k c
      -> maps_tree k v t.
    Admitted.
    Hint Resolve zip_maps_elim_c.

    Lemma zip_not_in_intro :
      forall {k t c},
      not_in_tree k t
      -> not_in_context k c
      -> not_in_tree k (zip t c).
    Admitted.
    Hint Resolve zip_not_in_intro.

    Lemma zip_not_in_elim_t :
      forall {k t c},
      not_in_tree k (zip t c)
      -> not_in_tree k t.
    Admitted.
    Hint Resolve zip_not_in_elim_t.

    Lemma zip_not_in_elim_c :
      forall {k t c},
      not_in_tree k (zip t c)
      -> not_in_context k c.
    Admitted.
    Hint Resolve zip_not_in_elim_c.

    Lemma zip_bst :
      forall {l_t u_t t l_r u_r c},
      bst_tree l_t u_t t
      -> bst_context l_r u_r l_t u_t c
      -> bst_tree l_r u_r (zip t c).
    Admitted.
    Hint Resolve zip_bst.

    Lemma zip_balance :
      forall {n t n' c},
      balance_tree n t
      -> balance_context n n' c
      -> balance_tree n' (zip t c).
    Admitted.
    Hint Resolve zip_balance.
    *)

    (* Lemmas about fuse *)

    Lemma fuse_maps_intro :
      forall {k v c c'},
      maps_context k v c \/ maps_context k v c'
      -> maps_context k v (fuse c c').
    Admitted.
    Hint Resolve fuse_maps_intro.

    (*
    Lemma fuse_maps_elim_c :
      forall {k v c c'},
      maps_context k v (fuse c c')
      -> not_in_context k c'
      -> in_context k c.
    Admitted.
    Hint Resolve fuse_maps_elim_c.

    Lemma fuse_maps_elim_c' :
      forall {k v c c'},
      maps_context k v (fuse c c')
      -> not_in_context k c
      -> in_context k c'.
    Admitted.
    Hint Resolve fuse_maps_elim_c'.

    Lemma fuse_not_in_intro :
      forall {k c c'},
      not_in_context k c
      -> not_in_context k c'
      -> not_in_context k (fuse c c').
    Admitted.
    Hint Resolve fuse_not_in_intro.

    Lemma fuse_not_in_elim_c :
      forall {k c c'},
      not_in_context k (fuse c c')
      -> not_in_context k c.
    Admitted.
    Hint Resolve fuse_not_in_elim_c.

    Lemma fuse_not_in_elim_c' :
      forall {k c c'},
      not_in_context k (fuse c c')
      -> not_in_context k c'.
    Admitted.
    Hint Resolve fuse_not_in_elim_c'.
    *)

    Lemma fuse_bst :
      forall {l_m u_m l_t u_t c l_r u_r c'},
      bst_context l_m u_m l_t u_t c
      -> bst_context l_r u_r l_m u_m c'
      -> bst_context l_r u_r l_t u_t (fuse c c').
    Admitted.
    Hint Resolve fuse_bst.

    Lemma fuse_balance :
      forall {n n' c n'' c'},
      balance_context n n' c
      -> balance_context n' n'' c'
      -> balance_context n n'' (fuse c c').
    Admitted.
    Hint Resolve fuse_balance.

    (* Lemmas about locate. *)

    Lemma locate_fail_eq :
      forall {k t} c, not_in_tree k t -> exists c', locate k t c = inl c'.
    Admitted.

    Lemma locate_success_eq :
      forall {k v t} c, maps_tree k v t -> exists l, locate k t c = inr (v,l).
    Admitted.

    Ltac locate_match_progress :=
      let Hex := fresh "Hex" in let c'  := fresh "c'"  in
      let l   := fresh "l"   in let Heq := fresh "Heq" in
      match goal with
      | [ |- context [ match locate ?k ?t ?c with _ => _ end ] ] =>
          match goal with
          | [ H : not_in_tree k t |- _ ] =>
              assert (exists c', locate k t c = inl c') as Hex
              ; [ eapply locate_fail_eq | destruct Hex as [c' Heq] ; rewrite Heq ]
          | [ H : maps_tree k ?v t |- _ ] =>
              assert (exists l, locate k t c = inr (v,l)) as Hex
              ; [ eapply locate_success_eq
                | destruct Hex as [l Heq] ; rewrite Heq
                ]
          | _ => in_tree_case k t ; locate_match_progress
          end
      | [ Hm : context [ match locate ?k ?t ?c with _ => _ end ] |- _ ] =>
          match goal with
          | [ H : not_in_tree k t |- _ ] =>
              assert (exists c', locate k t c = inl c') as Hex
              ; [ clear Hm ; eapply locate_fail_eq
                | destruct Hex as [c' Heq] ; rewrite Heq in Hm
                ]
          | [ H : maps_tree k ?v t |- _ ] =>
              assert (exists l, locate k t c = inr (v,l)) as Hex
              ; [ clear Hm ; eapply locate_success_eq
                | destruct Hex as [l Heq] ; rewrite Heq in Hm
                ]
          | _ => in_tree_case k t ; locate_match_progress
          end
      end.

    Lemma locate_fail_maps_intro :
      forall {k v k' t c c'},
      locate k' t c = inl c'
      -> maps_tree k v t \/ maps_context k v c
      -> maps_context k v c'.
    Admitted.
    Hint Resolve locate_fail_maps_intro.

    Lemma locate_fail_maps_elim_t :
      forall {k v k' t c c'},
      locate k' t c = inl c'
      -> maps_context k v c'
      -> not_in_context k c
      -> maps_tree k v t.
    Admitted.
    Hint Resolve locate_fail_maps_elim_t.

    Lemma locate_fail_maps_elim_c :
      forall {k v k' t c c'},
      locate k' t c = inl c'
      -> maps_context k v c'
      -> not_in_tree k t
      -> maps_context k v c.
    Admitted.
    Hint Resolve locate_fail_maps_elim_c.

    Lemma locate_fail_not_in_intro :
      forall {k t c c'},
      locate k t c = inl c'
      -> not_in_tree k t
      -> not_in_context k c
      -> not_in_context k c'.
    Admitted.
    Hint Resolve locate_fail_not_in_intro.

    (*

    Lemma locate_fail_not_in_elim_t :
      forall {k t c c'},
      locate k t c = inl c'
      -> not_in_context k c'
      -> not_in_tree k t.
    Admitted.
    Hint Resolve locate_fail_not_in_elim_t.

    Lemma locate_fail_not_in_elim_c :
      forall {k t c c'},
      locate k t c = inl c'
      -> not_in_context k c'
      -> not_in_context k c.
    Admitted.
    Hint Resolve locate_fail_not_in_elim_c.

    *)
    Lemma locate_success_not_in_k :
      forall {k t c v l},
      locate k t c = inr (v,l)
      -> not_in_location k l.
    Admitted.
    Hint Resolve locate_success_not_in_k.
    (*

    Ltac pose_locate_success_not_in_k :=
      let Hnotin := fresh "Hnotin" in let n := fresh "n" in
      let finish Heq k l :=
        assert (not_in_location k l) as Hnotin
        ; [ eapply (locate_success_not_in_k Heq) ; clear Heq
          | inversion Hnotin ; subst ; clear Hnotin
          ]
      in
      match goal with
      | [ Heq : locate ?k ?t ?c = inr (_,TwoHole_l ?tl ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : not_in_tree k tl |- _ ] => fail 1
          | _ => finish Heq k (TwoHole_l tl tr c')
          end
      | [ Heq : locate ?k ?t ?c = inr (_,ThreeLeftHole_l ?tl ?tm ?pr ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : not_in_tree k tl |- _ ] => fail 1
          | _ => finish Heq k (ThreeLeftHole_l tl tm pr tr c')
          end
      | [ Heq : locate ?k ?t ?c = inr (_,ThreeRightHole_l ?tl ?pl ?tm ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : not_in_tree k tl |- _ ] => fail 1
          | _ => finish Heq k (ThreeRightHole_l tl pl tm tr c')
          end
      end.
    *)

    Lemma locate_success_maps_intro :
      forall {k v k' v' t c l},
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_tree k v t \/ maps_context k v c
      -> maps_location k v l.
    Admitted.
    Hint Resolve locate_success_maps_intro.

    Lemma locate_success_maps_intro_two_c :
      forall {k v k' v' t c tl tr c'},
      locate k' t c = inr (v',TwoHole_l tl tr c')
      -> k /~= k'
      -> maps_tree k v t \/ maps_context k v c
      -> not_in_tree k tl
      -> not_in_tree k tr
      -> maps_context k v c'.
    Admitted.
    Hint Resolve locate_success_maps_intro_two_c.

    (*
    Ltac pose_locate_success_maps_intro :=
      let Hmaps := fresh "Hmaps" in
      let finish Heq k v l :=
        assert (maps_location k v l) as Hmaps
        ; [ eapply (locate_success_maps_intro Heq) ; clear Heq
          | inversion Hmaps ; subst ; clear Hmaps ]
      in
      match goal with
      | [ H : maps_tree ?k ?v ?t , Hneq : ?k /~= ?k' , Heq : locate ?k' ?t _ = inr (_,?l) |- _ ] =>
          match l with
          | TwoHole_l ?tl ?tr ?c' =>
              match goal with
              | [ H : maps_tree k v tl |- _ ] => fail 1
              | [ H : maps_tree k v tr |- _ ] => fail 1
              | [ H : maps_context k v c' |- _ ] => fail 1
              | _ => finish Heq k v l
          | ThreeLeftHole_l ?tl ?tm ?pr ?tr ?c' =>
              | [ H : 
            finish Heq c' k v l
          | ThreeRightHole_l ?tl ?pl ?tm ?tr ?c' => finish Heq c' k v l
          end
      end.
    *)

    Lemma locate_success_maps_elim_t :
      forall {k v k' v' t c l},
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_location k v l
      -> not_in_context k c
      -> maps_tree k v t.
    Admitted.
    Hint Resolve locate_success_maps_elim_t.

    Lemma locate_success_maps_elim_c :
      forall {k v k' v' t c l},
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_location k v l
      -> not_in_tree k t
      -> maps_context k v c.
    Admitted.
    Hint Resolve locate_success_maps_elim_c.

    Lemma locate_fail_bst_ex :
      forall {k l_t u_t t l_r u_r c c'},
      locate k t c = inl c'
      -> not_in_tree k t
      -> bst_tree l_t u_t t
      -> bst_context l_r u_r l_t u_t c
      -> exists l u, bst_context l_r u_r l u c' /\ l <= Extend k <= u.
    Admitted.

    Lemma locate_fail_bst_top_ex :
      forall {k l_t u_t t c'},
      locate k t Top_c = inl c'
      -> not_in_tree k t
      -> bst_tree l_t u_t t
      -> exists l u, bst_context l_t u_t l u c' /\ l <= Extend k <= u.
    Admitted.

    Ltac pose_locate_fail_bst_top_ex :=
      match goal with
      | [ H : bst_tree ?l_t ?u_t ?t , Heq : locate ?k ?t Top_c = inl ?c' |- _] =>
          match goal with
          | [ H : bst_context _ _ _ _ c' |- _ ] => fail 1
          | _ =>
            let Hex := fresh "Hex" in let l := fresh "l" in let u := fresh "u" in
            assert (exists l u, bst_context l_t u_t l u c' /\ l <= Extend k <= u) as Hex
            ; [ eapply (locate_fail_bst_ex Heq) ; clear Heq
              | destruct Hex as [l Hex] ; destruct Hex as [u Hex] ; destruct Hex
              ]
          end
      end.

    Lemma locate_success_bst :
      forall {k l_t u_t t l_r u_r c v l},
      locate k t c = inr (v,l)
      -> maps_tree k v t
      -> bst_tree l_t u_t t
      -> bst_context l_r u_r l_t u_t c
      -> bst_location l_r u_r (Extend k) l.
    Admitted.
    Hint Resolve locate_success_bst.

    Lemma locate_fail_balance :
      forall {k n t n' c c'},
      locate k t c = inl c'
      -> not_in_tree k t
      -> balance_tree n t
      -> balance_context n n' c
      -> balance_context 0 n' c'.
    Admitted.
    Hint Resolve locate_fail_balance.

    Lemma locate_success_balance :
      forall {k n t n' c v l},
      locate k t c = inr (v,l)
      -> maps_tree k v t
      -> balance_tree n t
      -> balance_context n n' c
      -> balance_location n' l.
    Admitted.
    Hint Resolve locate_success_balance.

    Ltac pose_locate_success_balance :=
      let Hex := fresh "Hex" in let Hbal := fresh "Hbal" in let n := fresh "n" in
      let finish Heq c' l :=
        match goal with
        | [ Hbal : balance_context _ _ c' |- _ ] => fail 1
        | _ => assert (exists n, balance_location n l) as Hex
               ; [ econstructor ; eapply (locate_success_balance Heq) ; clear Heq
                 | destruct Hex as [n Hbal] ; inversion Hbal ; subst ; clear Hbal ]
        end
      in
      match goal with
      | [ Heq : locate _ _ _ = inr (_,?l) |- _ ] =>
          match l with
          | TwoHole_l _ _ ?c' => finish Heq c' l
          | ThreeLeftHole_l _ _ _ _ ?c' => finish Heq c' l
          | ThreeRightHole_l _ _ _ _ ?c' => finish Heq c' l
          end
      end.

    (* Lemmas about lookup. *)

    Lemma lookup_success_eq : forall {k v t}, maps_tree k v t -> lookup k t = Some v.
    Admitted.
    (*
    Proof. intros k v t Ht ; unfold lookup ; locate_match_progress ; eauto. Qed.
    *)

    Program Definition lookup_total k t (Ht:in_tree k t) : V :=
      match lookup k t with
      | None => False_rect _ _
      | Some v => v
      end.
    Next Obligation.
      destruct (in_to_maps_ex Ht) as [v Hmaps] ; rewrite (lookup_success_eq Hmaps) in * ; congruence.
    Qed.

    (* Lemmas about fill_location *)

    Lemma fill_location_maps_k :
      forall {k v l},
      not_in_location k l
      -> maps_tree k v (fill_location (k,v) l).
    Admitted.
    Hint Resolve fill_location_maps_k.

    Lemma fill_location_maps_intro :
      forall {k k' v v' v'' t c l},
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_tree k v t \/ maps_context k v c
      -> maps_tree k v (fill_location (k',v'') l).
    Admitted.
    Hint Resolve fill_location_maps_intro.

    Lemma fill_location_maps_elim_t :
      forall {k k' v v' v'' t c l},
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_tree k v (fill_location (k',v'') l)
      -> not_in_context k c
      -> maps_tree k v t.
    Admitted.
    Hint Resolve fill_location_maps_elim_t.

    Lemma fill_location_maps_elim_c :
      forall {k k' v v' v'' t c l},
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_tree k v (fill_location (k',v'') l)
      -> not_in_tree k t
      -> maps_context k v c.
    Admitted.
    Hint Resolve fill_location_maps_elim_c.

    Lemma fill_location_bst :
      forall {k v l_r u_r l},
      bst_location l_r u_r (Extend k) l
      -> bst_tree l_r u_r (fill_location (k,v) l).
    Admitted.
    Hint Resolve fill_location_bst.

    Lemma fill_location_balance :
      forall {k v n l},
      balance_location n l
      -> balance_tree n (fill_location (k,v) l).
    Admitted.
    Hint Resolve fill_location_balance.

    (* Lemmas about locate_greatest *)

    Lemma locate_greatest_fail_eq : forall {t c}, empty_tree t -> locate_greatest t c = None.
    Admitted.

    Lemma locate_greatest_success_eq :
      forall {t c}, not_empty_tree t -> exists k v lM, locate_greatest t c = Some ((k,v),lM).
    Admitted.

    Ltac locate_greatest_match_progress :=
      let Hex := fresh "Hex" in let k   := fresh "k'"  in let v := fresh "v'" in
      let lM  := fresh "lM'" in let Heq := fresh "Heq" in
      match goal with
      | [ |- context [ match locate_greatest ?t ?c with _ => _ end ] ] =>
          match goal with
          | [ H : empty_tree t |- _ ] =>
              assert (locate_greatest t c = None) as Heq
              ; [ eapply locate_greatest_fail_eq | rewrite Heq ]
          | [ H : not_empty_tree t |- _ ] =>
              assert (exists k v lM, locate_greatest t c = Some ((k,v),lM)) as Hex
              ; [ eapply locate_greatest_success_eq
                | destruct Hex as [k Hex] ; destruct Hex as [v Hex]
                  ; destruct Hex as [lM Heq] ; rewrite Heq ]
          | _ => destruct (empty_tree_dp t) ; locate_greatest_match_progress
          end
      | [ Hm : context [ match locate_greatest ?t ?c with _ => _ end ] |- _ ] =>
          match goal with
          | [ H : empty_tree t |- _ ] =>
              assert (locate_greatest t c = None) as Heq
              ; [ clear Hm ; eapply locate_greatest_fail_eq | rewrite Heq in Hm ]
          | [ H : not_empty_tree t |- _ ] =>
              assert (exists k v lM, locate_greatest t c = Some ((k,v),lM)) as Hex
              ; [ clear Hm ; eapply locate_greatest_success_eq
                | destruct Hex as [k Hex] ; destruct Hex as [v Hex]
                  ; destruct Hex as [lM Heq] ; rewrite Heq in Hm ]
          | _ => destruct (empty_tree_dp t) ; locate_greatest_match_progress
          end
      end.

    Lemma locate_greatest_two_maps_intro_c' :
      forall {k k' v v' t c  c'},
      locate_greatest t c = Some ((k',v'),inl c')
      -> maps_tree k v t
      -> k /~= k'
      -> maps_context k v c'.
    Admitted.
    Hint Resolve locate_greatest_two_maps_intro_c'.

    (*
    (*
    Lemma locate_greatest_success_result_ineq :
      forall {k k' v t c cM},
      locate_greatest t c = Some (k',v,cM)
      -> not_in_tree k t
      -> k /~= k'.
    Admitted.
    Hint Resolve locate_greatest_success_result_ineq.

    Lemma locate_greatest_success_three_p_ineq :
      forall {k k' v' t c k'' v'' c'},
      locate_greatest t c = Some ((k',v'),inr((k'',v''),c'))
      -> not_in_tree k t
      -> k /~= k''.
    Admitted.
    Hint Resolve locate_greatest_success_three_p_ineq.
*)

    Lemma locate_greatest_two_maps_intro_k :
      forall {k k' v v' t c  c'},
      locate_greatest t c = Some ((k',v'),inl c')
      -> maps_tree k v t
      -> not_in_context k c'
      -> k /~= k'.
    Admitted.
    Hint Resolve locate_greatest_two_maps_intro_k.

    Lemma locate_greatest_two_maps_intro_v :
      forall {k k' v v' t c  c'},
      locate_greatest t c = Some ((k',v'),inl c')
      -> maps_tree k v t
      -> not_in_context k c'
      -> v = v'.
    Admitted.
    Hint Resolve locate_greatest_two_maps_intro_v.

    Lemma locate_greatest_success_two_not_in :
      forall {k k' v' t c c'},
      locate_greatest t c = Some ((k',v'), inl c')
      -> not_in_tree k t
      -> not_in_context k c
      -> not_in_context k c'.
    Admitted.
    Hint Resolve locate_greatest_success_two_not_in.

    Lemma locate_greatest_success_three_in :
      forall {k k' v' k'' v'' t c  c'},
      locate_greatest t c = Some ((k',v'),inr ((k'',v''),c'))
      -> in_tree k t
      -> k ~= k' \/ k ~= k'' \/ in_context k c'.
    Admitted.

    Lemma locate_greatest_success_three_not_in :
      forall {k k' v' k'' v'' t c c'},
      locate_greatest t c = Some ((k',v'), inr((k'',v''),c'))
      -> not_in_tree k t
      -> not_in_context k c
      -> not_in_context k c'.
    Admitted.
    Hint Resolve locate_greatest_success_three_not_in.

    Lemma locate_greatest_success_two_bst :
      forall {k v l_t u_t t l_r u_r c c'},
      locate_greatest t c = Some ((k,v), inl c')
      -> bst_tree l_t u_t t
      -> bst_context l_r u_r l_t u_t c
      -> exists l_p u_p, bst_context l_r (Extend k) l_p u_p c' /\ Extend k <= u_t.
    Admitted.
    *)

    Lemma locate_greatest_success_two_balance :
      forall {n t n' c k v c'},
      locate_greatest t c = Some ((k,v),inl c')
      -> balance_tree n t
      -> balance_context n n' c
      -> balance_context (0+1) n' c'.
    Admitted.
    Hint Resolve locate_greatest_success_two_balance.

    (* Lemmas about insert_up *)

    Lemma insert_up_maps_k :
      forall {k v tl tr c},
      not_in_context k c
      -> maps_tree k v (insert_up (tl,(k,v),tr) c).
    Admitted.
    Hint Resolve insert_up_maps_k.

    Lemma insert_up_maps_intro :
      forall {k k' v v' tl tr c},
      k /~= k'
      -> maps_context k v c
      -> maps_tree k v (insert_up (tl,(k',v'),tr) c).
    Admitted.
    Hint Resolve insert_up_maps_intro.

    Lemma insert_up_maps_elim_c :
      forall {k k' v v' tl tr c},
      k /~= k'
      -> maps_tree k v (insert_up (tl,(k',v'),tr) c)
      -> not_in_tree k tl
      -> not_in_tree k tr
      -> maps_context k v c.
    Admitted.
    Hint Resolve insert_up_maps_elim_c.

    Lemma insert_up_bst :
      forall {k v tl tr l_r u_r l_t u_t c},
      bst_context l_r u_r l_t u_t c
      -> bst_tree l_t (Extend k) tl
      -> bst_tree (Extend k) u_t tr
      -> bst_tree l_r u_r (insert_up (tl,(k,v),tr) c).
    Admitted.
    Hint Resolve insert_up_bst.

    Lemma insert_up_balance :
      forall n tl k v tr n' c,
      balance_tree n tl
      -> balance_tree n tr
      -> balance_context n n' c
      -> exists n'', balance_tree n'' (insert_up (tl,(k,v),tr) c).
    Admitted.
    Hint Resolve insert_up_balance.

    (* Lemmas about insert_with. *)

    Lemma insert_with_maps_k :
      forall {f k v v' t},
      maps_tree k v' t
      -> maps_tree k (f v v') (insert_with f k v t).
    Proof. intros ; unfold insert_with ; locate_match_progress ; eauto. Qed.

    Lemma insert_with_not_in_k :
      forall {f k v t}, not_in_tree k t -> maps_tree k v (insert_with f k v t).
    Proof. intros ; unfold insert_with ; locate_match_progress ; eauto. Qed.

    Lemma insert_with_maps_intro :
      forall {f k k' v v' t},
      k /~= k'
      -> maps_tree k v t
      -> maps_tree k v (insert_with f k' v' t).
    Proof. intros ; unfold insert_with ; in_tree_case k' t ; locate_match_progress ; eauto. Qed.

    Lemma insert_with_maps_elim :
      forall {f k k' v v' t},
      k /~= k'
      -> maps_tree k v (insert_with f k' v' t)
      -> maps_tree k v t.
    Proof. intros ; unfold insert_with in * ; in_tree_case k' t ; locate_match_progress ; eauto. Qed.

    Lemma insert_with_bst :
      forall {f k v l_t u_t t},
      l_t <= Extend k <= u_t
      -> bst_tree l_t u_t t
      -> bst_tree l_t u_t (insert_with f k v t).
    Proof.
      intros ; unfold insert_with in * ; in_tree_case k' t
      ; locate_match_progress ; try pose_locate_fail_bst_top_ex ; eauto.
    Qed.

    Lemma insert_with_balance :
      forall f k v n t,
      balance_tree n t -> exists n', balance_tree n' (insert_with f k v t).
    Proof. intros ; unfold insert_with in * ; in_tree_case k t ; locate_match_progress ; eauto. Qed.

    (* Lemmas about remove_up *)

    Lemma remove_up_wf :
      forall {n t n' c},
      balance_tree n t -> balance_context (n+1) n' c -> exists t', remove_up t c = Some t'.
    Admitted.
    (*
    Proof.
      intros n t n' c ; gd n' ; gd t ; gd n ; induction c ; intros ; simpl
      ; repeat mysimp || atom_match_drill || auto ; eauto.
    Qed.
    *)

    Ltac remove_up_wf_progress_goal :=
      let Heq := fresh "Heq" in
      let t' := fresh "t'" in
      match goal with
      | [ |- context [ remove_up ?t ?c ] ] =>
          assert (exists t', remove_up t c = Some t') as Hex
          ; [ eapply remove_up_wf
            | destruct Hex as [t' Heq] ; rewrite Heq
            ]
      end.

    Lemma remove_up_maps_intro :
      forall {k v t c t'},
      remove_up t c = Some t'
      -> maps_tree k v t \/ maps_context k v c
      -> maps_tree k v t'.
    Admitted.
    Hint Resolve remove_up_maps_intro.

    (*
    Lemma remove_up_not_in :
      forall {k t c t'},
      remove_up t c = Some t'
      -> not_in_tree k t
      -> not_in_context k c
      -> not_in_tree k t'.
    Admitted.
    Hint Resolve remove_up_not_in.

    *)

    (* Lemmas about remove *)

    Lemma remove_wf :
      forall {k n t},
      balance_tree n t -> exists t' vM, remove k t = Some (t',vM).
    Admitted.
    (*
    Proof.
      intros ; unfold remove
      ; repeat
          mysimp || locate_match_progress || locate_greatest_match_progress
          || let_pair_drill || atom_match_drill
          || pose_locate_success_balance
          || remove_up_wf_progress_goal
      ; eauto ; try (compute ; eauto ; fail).
    Qed.
    *)
      
    Lemma remove_wf_maps_k :
      forall k v n t,
      balance_tree n t -> maps_tree k v t -> exists t', remove k t = Some (t',Some v).
    Admitted.
    (*
    Proof.
      intros ; unfold remove
      ; repeat
          mysimp
          || locate_match_progress || locate_greatest_match_progress
          || let_pair_drill || atom_match_drill
          || pose_locate_success_balance
          || remove_up_wf_progress_goal
      ; eauto ; try (compute ; eauto ; fail).
    Qed.
    *)

    Lemma remove_wf_not_in_k :
      forall k n t,
      balance_tree n t -> not_in_tree k t -> exists t', remove k t = Some (t',None).
    Admitted.
    (*
    Proof. intros ; unfold remove ; repeat mysimp || locate_match_progress ; eauto. Qed.
    *)

    Ltac fmap_success_eq :=
      match goal with
      | [ H : fmap ?f ?xM = Some ?x |- _ ] =>
          let X := fresh "X" in
          remember xM as X ; flip_eqn xM ; destruct X ; unfold fmap in * ; simpl in *
          ; try congruence
      end.
    Ltac mysimp2 := mysimp1 || fmap_success_eq.
    Ltac mysimp ::= mysimp2.

    Lemma locate_greatest_maps_two_elim_k :
      forall {t k v c},
      locate_greatest t c = Some (k,v,inl c)
      -> not_in_context k c
      -> maps_tree k v t.
    Admitted.
    Hint Resolve locate_greatest_maps_two_elim_k.

    Lemma remove_maps_intro :
      forall k v k' n t t' vM,
      remove k' t = Some (t',vM)
      -> k /~= k'
      -> balance_tree n t
      -> maps_tree k v t
      -> maps_tree k v t'.
    Proof.
      intros ; unfold remove in *
      ; repeat
          mysimp
          || locate_match_progress
          || locate_greatest_match_progress
          || let_pair_drill || atom_match_drill
          || pose_locate_success_balance
      ; eauto.
      - eapply remove_up_maps_intro ; eauto ; right.
        assert (maps_location k v (TwoHole_l t0 t1 c)) as Hml ; [eauto|]
        ; inversion Hml ; subst ; clear Hml ; eauto.
        remember (k ~=! k'1) as m ; destruct m ; repeat mysimp ; eauto.
        admit.
      - 
        admit.
        admit.
        eauto.
        eauto.
        Show.
        admit.
        eapply fuse_maps_intro ; left.
        left.
        eapply locate_greatest_two_maps_intro_c' ; eauto.



        ; in_tree_case k t1 ; eauto.
      pose_locate_success_maps_intro ; eauto.
        repeat
          mysimp
          || locate_match_progress
          || locate_greatest_match_progress
          || let_pair_drill || atom_match_drill
          || pose_locate_success_balance
          || pose_locate_success_maps_intro.
      mysimp.
      pose_locate_success_maps_intro.
      let Hmaps := fresh "Hmaps" in
      let finish Heq c' k v l :=
        match goal with
        | [ H : maps_context k v c' |- _ ] => fail 1
        | _ => assert (maps_location k v l) as Hmaps
               ; [ eapply (locate_success_maps_intro Heq) ; clear Heq
                 | inversion Hmaps ; subst ; clear Hmaps ]
        end
      in
      match goal with
      | [ H : maps_tree ?k ?v ?t , Hneq : ?k /~= ?k' , Heq : locate ?k' ?t _ = inr (_,?l |- _ ] =>
          match l with
          | TwoHole_l _ _ ?c' => idtac
          | ThreeLeftHole_l _ _ _ _ ?c' => idtac
          | ThreeRightHole_l _ _ _ _ ?c' => idtac
          end
      end.

      - eapply remove_up_in ; eauto.
        right ; eauto.
        assert (in_location k (TwoHole_l t0 t1 c)) as H'
        ; [|inversion H' ; subst ; clear H'] ; eauto.
        assert (k ~= k'1 \/ in_context k c0) as H'
        ; [eapply locate_greatest_success_two_in|destruct H'] ; eauto.
      - assert (in_location k (TwoHole_l t0 t1 c)) as H'
        ; [|inversion H' ; subst ; clear H'] ; eauto.
        + assert (k ~= k'1 \/ k ~= k0 \/ in_context k c0) as H'
          ; [eapply locate_greatest_success_three_in|destruct H' as [Dis1|H'] ; [|destruct H']]
          ; eauto.
          eapply zip_in.
        + assert (k ~= k'1 \/ k ~= k0 \/ in_context k c0) as H'
          ; [eapply locate_greatest_success_three_in|] ; eauto.
          destruct H' as [f|H'].
        eapply fuse_in_c'.
        econstructor.
        eapply locate_greatest_success_result_ineq.
        eauto.
      ; eauto 30.
        
    Lemma remove_not_in :
      forall k n t t' vM,
      remove k t = Some (t',vM) -> balance_tree n t -> not_in_tree k t'.
    Admitted.
    (*
    Proof.
      intros ; unfold remove in *
      ; repeat
          mysimp
          || match goal with p : prod K V |- _ => destruct p end
          || locate_match_progress
          || locate_greatest_match_progress
          || let_pair_drill || atom_match_drill
          || fmap_success_eq
      ; eauto 30.
    Qed.
    *)


  
  
End TwoThreeTreesWF.
