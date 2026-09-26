import Erdos1220.ConditionAlgebra
import Erdos1220.PureExtension
import Erdos1220.BlockPreservingClosure

/-! Replace a history prefix by another actual history with the same endpoint.
All suffix transitions are retained. This is the splice used by a single flip. -/

open Cardinal Set Order

universe u

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}
variable (H K : History V I block μ hμ) (hL : K.length ≤ H.length)
  (hend : K.last = H.state K.length hL)

open scoped Classical in
noncomputable def spliceState (i : Ordinal.{u}) (hi : i ≤ H.length) :
    BasicCondition V I block μ :=
  if hk : i ≤ K.length then K.state i hk else H.state i hi

theorem spliceState_prefix (i : Ordinal.{u}) (hi : i ≤ H.length) (hk : i ≤ K.length) :
    H.spliceState K i hi = K.state i hk := by
  simp only [spliceState, dite_eq_left hk]

include hend in
theorem spliceState_suffix (i : Ordinal.{u}) (hi : i ≤ H.length) (hk : K.length ≤ i) :
    H.spliceState K i hi = H.state i hi := by
  classical
  by_cases heq : i = K.length
  · subst i
    exact (H.spliceState_prefix K _ hi le_rfl).trans hend
  · simp only [spliceState, dite_eq_right (not_le_of_gt (lt_of_le_of_ne hk (Ne.symm heq)))]

include hend in
theorem spliceState_increasing (i j : Ordinal.{u}) (hi : i ≤ H.length)
    (hj : j ≤ H.length) (hij : i ≤ j) :
    Extends (H.spliceState K i hi) (H.spliceState K j hj) := by
  classical
  by_cases hjk : j ≤ K.length
  · rw [H.spliceState_prefix K i hi (hij.trans hjk), H.spliceState_prefix K j hj hjk]
    exact K.increasing i j _ _ hij
  · have hkj : K.length ≤ j := (lt_of_not_ge hjk).le
    rw [H.spliceState_suffix K hL hend j hj hkj]
    by_cases hik : i ≤ K.length
    · rw [H.spliceState_prefix K i hi hik]
      have he := K.state_extends_last i hik
      rw [hend] at he
      exact he.trans (H.increasing K.length j hL hj hkj)
    · rw [H.spliceState_suffix K hL hend i hi (lt_of_not_ge hik).le]
      exact H.increasing i j hi hj hij

open scoped Classical in
noncomputable def spliceStep (i : Ordinal.{u}) (hi : Order.succ i ≤ H.length) :
    Transition hμ (H.spliceState K i ((Order.le_succ i).trans hi))
      (H.spliceState K (Order.succ i) hi) :=
  if hk : Order.succ i ≤ K.length then
    (K.step i hk).cast
      (H.spliceState_prefix K i _ ((Order.le_succ i).trans hk)).symm
      (H.spliceState_prefix K (Order.succ i) hi hk).symm
  else
    (H.step i hi).cast
      (H.spliceState_suffix K hL hend i _
        (Order.lt_succ_iff.mp (lt_of_not_ge hk))).symm
      (H.spliceState_suffix K hL hend (Order.succ i) hi (lt_of_not_ge hk).le).symm

include hend in
theorem splice_limit_support (i : Ordinal.{u}) (hi : i ≤ H.length)
    (hlim : Order.IsSuccLimit i) (x : V) :
    x ∈ (H.spliceState K i hi).support ↔
      ∃ j, ∃ hji : j < i, x ∈ (H.spliceState K j (hji.le.trans hi)).support := by
  classical
  constructor
  · intro hx
    by_cases hk : i ≤ K.length
    · rw [H.spliceState_prefix K i hi hk] at hx
      obtain ⟨j, hji, hjx⟩ := (K.limit_support i hk hlim x).mp hx
      refine ⟨j, hji, ?_⟩
      rw [H.spliceState_prefix K j _ (hji.le.trans hk)]
      exact hjx
    · have hki : K.length < i := lt_of_not_ge hk
      rw [H.spliceState_suffix K hL hend i hi hki.le] at hx
      obtain ⟨j, hji, hjx⟩ := (H.limit_support i hi hlim x).mp hx
      by_cases hkj : K.length ≤ j
      · refine ⟨j, hji, ?_⟩
        rw [H.spliceState_suffix K hL hend j _ hkj]
        exact hjx
      · refine ⟨K.length, hki, ?_⟩
        rw [H.spliceState_suffix K hL hend K.length _ le_rfl]
        exact (H.increasing j K.length (hji.le.trans hi) hL (lt_of_not_ge hkj).le).1 hjx
  · rintro ⟨j, hji, hjx⟩
    exact (H.spliceState_increasing K hL hend j i _ hi hji.le).1 hjx

include hend in
theorem splice_limit_blue (i : Ordinal.{u}) (hi : i ≤ H.length)
    (hlim : Order.IsSuccLimit i) (x y : V) :
    (H.spliceState K i hi).blue x y ↔
      ∃ j, ∃ hji : j < i, (H.spliceState K j (hji.le.trans hi)).blue x y := by
  classical
  constructor
  · intro hb
    by_cases hk : i ≤ K.length
    · rw [H.spliceState_prefix K i hi hk] at hb
      obtain ⟨j, hji, hjb⟩ := (K.limit_blue i hk hlim x y).mp hb
      refine ⟨j, hji, ?_⟩
      rw [H.spliceState_prefix K j _ (hji.le.trans hk)]
      exact hjb
    · have hki : K.length < i := lt_of_not_ge hk
      rw [H.spliceState_suffix K hL hend i hi hki.le] at hb
      obtain ⟨j, hji, hjb⟩ := (H.limit_blue i hi hlim x y).mp hb
      by_cases hkj : K.length ≤ j
      · refine ⟨j, hji, ?_⟩
        rw [H.spliceState_suffix K hL hend j _ hkj]
        exact hjb
      · refine ⟨K.length, hki, ?_⟩
        rw [H.spliceState_suffix K hL hend K.length _ le_rfl]
        obtain ⟨hx, hy⟩ := (H.state j (hji.le.trans hi)).blue_support hjb
        exact ((H.increasing j K.length (hji.le.trans hi) hL (lt_of_not_ge hkj).le).2
          x hx y hy).mpr hjb
  · rintro ⟨j, hji, hjb⟩
    obtain ⟨hx, hy⟩ := (H.spliceState K j (hji.le.trans hi)).blue_support hjb
    exact ((H.spliceState_increasing K hL hend j i _ hi hji.le).2 x hx y hy).mpr hjb

noncomputable def splice : History V I block μ hμ where
  length := H.length
  length_lt := H.length_lt
  state i hi := H.spliceState K i hi
  increasing i j hi hj hij := H.spliceState_increasing K hL hend i j hi hj hij
  initial_red := by rw [H.spliceState_prefix K 0 zero_le zero_le]; exact K.initial_red
  initial_block_injective := by
    rw [H.spliceState_prefix K 0 zero_le zero_le]; exact K.initial_block_injective
  initial_nontrivial := by
    rw [H.spliceState_prefix K 0 zero_le zero_le]; exact K.initial_nontrivial
  step i hi := H.spliceStep K hL hend i hi
  limit_support i hi hlim x := H.splice_limit_support K hL hend i hi hlim x
  limit_blue i hi hlim x y := H.splice_limit_blue K hL hend i hi hlim x y

theorem splice_last : (H.splice K hL hend).last = H.last :=
  H.spliceState_suffix K hL hend H.length le_rfl hL

theorem spliceStep_heq_prefix (i : Ordinal.{u}) (hi : Order.succ i ≤ H.length)
    (hk : Order.succ i ≤ K.length) :
    HEq (H.spliceStep K hL hend i hi) (K.step i hk) := by
  unfold spliceStep
  split
  · exact Transition.cast_heq _ _ _
  · contradiction

theorem spliceStep_heq_suffix (i : Ordinal.{u}) (hi : Order.succ i ≤ H.length)
    (hk : ¬ Order.succ i ≤ K.length) :
    HEq (H.spliceStep K hL hend i hi) (H.step i hi) := by
  unfold spliceStep
  split
  · contradiction
  · exact Transition.cast_heq _ _ _

theorem pureExtends_splice : PureExtends K (H.splice K hL hend) := by
  refine ⟨hL, ?_, ?_⟩
  · intro i hi
    exact (H.spliceState_prefix K i (hi.trans hL) hi).symm
  · intro i hi
    exact (H.spliceStep_heq_prefix K hL hend i (hi.trans hL) hi).symm

theorem splice_blockPreserving (hH : H.BlockPreserving) (hK : K.BlockPreserving) :
    (H.splice K hL hend).BlockPreserving := by
  intro i hi
  change (H.spliceStep K hL hend i hi).iso.PreservesBlocks
  by_cases hk : Order.succ i ≤ K.length
  · exact (transition_preservesBlocks_iff_of_heq
      (H.spliceState_prefix K i _ ((Order.le_succ i).trans hk))
      (H.spliceState_prefix K (Order.succ i) hi hk)
      (H.spliceStep_heq_prefix K hL hend i hi hk)).mpr (hK i hk)
  · exact (transition_preservesBlocks_iff_of_heq
      (H.spliceState_suffix K hL hend i _ (Order.lt_succ_iff.mp (lt_of_not_ge hk)))
      (H.spliceState_suffix K hL hend (Order.succ i) hi (lt_of_not_ge hk).le)
      (H.spliceStep_heq_suffix K hL hend i hi hk)).mpr (hH i hi)

end Erdos1220.History

#print axioms Erdos1220.History.pureExtends_splice
#print axioms Erdos1220.History.splice_blockPreserving
