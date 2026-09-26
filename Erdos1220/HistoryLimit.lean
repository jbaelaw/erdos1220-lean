import Erdos1220.PureExtension

/-!
# Bounded coherent unions of histories

A nonempty pure-increasing chain of at most `μ` histories has a coherent
union whenever its supremum length is still below `(succ μ).ord`. The
construction preserves actual transition witnesses, not only terminal
colorings. This is a pure-order result; it does not assert closure of the
full weak forcing order.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- Explicit data for a bounded supremum of a nonempty coherent chain. -/
structure PureChain (J : Type u) [LinearOrder J] [Nonempty J] where
  history : J → History V I block μ hμ
  small : #J ≤ μ
  increasing : ∀ j k, j ≤ k → PureExtends (history j) (history k)
  length : Ordinal.{u}
  length_lt : length < (Order.succ μ).ord
  length_le : ∀ j, (history j).length ≤ length
  cofinal : ∀ i, i < length → ∃ j, i < (history j).length

namespace PureChain

variable {J : Type u} [LinearOrder J] [Nonempty J]
variable (C : PureChain (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ) J)

def top : BasicCondition V I block μ :=
  chainUnion (fun j => (C.history j).last) C.small hμ

theorem extends_top (j : J) : Extends (C.history j).last C.top :=
  extends_chainUnion _ C.small hμ
    (fun j k hjk => (C.increasing j k hjk).last_extends) j

theorem states_agree (j k : J) (i : Ordinal.{u})
    (hj : i ≤ (C.history j).length) (hk : i ≤ (C.history k).length) :
    (C.history j).state i hj = (C.history k).state i hk := by
  exact ((C.increasing j (max j k) (le_max_left _ _)).state_eq i hj).trans
    ((C.increasing k (max j k) (le_max_right _ _)).state_eq i hk).symm

theorem steps_agree (j k : J) (i : Ordinal.{u})
    (hj : Order.succ i ≤ (C.history j).length)
    (hk : Order.succ i ≤ (C.history k).length) :
    HEq ((C.history j).step i hj) ((C.history k).step i hk) := by
  exact ((C.increasing j (max j k) (le_max_left _ _)).step_heq i hj).trans
    ((C.increasing k (max j k) (le_max_right _ _)).step_heq i hk).symm

def Covered (i : Ordinal.{u}) : Prop := ∃ j, i ≤ (C.history j).length

noncomputable def representative (i : Ordinal.{u}) (hi : C.Covered i) : J :=
  Classical.choose hi

theorem representative_covers (i : Ordinal.{u}) (hi : C.Covered i) :
    i ≤ (C.history (C.representative i hi)).length := Classical.choose_spec hi

open scoped Classical in
noncomputable def state (i : Ordinal.{u}) : BasicCondition V I block μ :=
  if hi : C.Covered i then
    (C.history (C.representative i hi)).state i (C.representative_covers i hi)
  else C.top

theorem state_eq (j : J) (i : Ordinal.{u}) (hi : i ≤ (C.history j).length) :
    C.state i = (C.history j).state i hi := by
  have hcov : C.Covered i := ⟨j, hi⟩
  simp only [state, dite_eq_left hcov]
  exact C.states_agree _ j i _ hi

theorem state_top (i : Ordinal.{u}) (hi : ¬ C.Covered i) : C.state i = C.top := by
  simp only [state, dite_eq_right hi]

theorem covered_of_lt (i : Ordinal.{u}) (hi : i < C.length) : C.Covered i := by
  obtain ⟨j, hj⟩ := C.cofinal i hi
  exact ⟨j, hj.le⟩

theorem covered_zero : C.Covered 0 :=
  ⟨Classical.choice inferInstance, bot_le⟩

theorem covered_succ (i : Ordinal.{u}) (hi : Order.succ i ≤ C.length) :
    C.Covered (Order.succ i) := by
  obtain ⟨j, hj⟩ := C.cofinal i ((Order.lt_succ i).trans_le hi)
  exact ⟨j, Order.succ_le_of_lt hj⟩

theorem state_increasing (i k : Ordinal.{u}) (hik : i ≤ k) :
    Extends (C.state i) (C.state k) := by
  classical
  by_cases hk : C.Covered k
  · obtain ⟨j, hj⟩ := hk
    rw [C.state_eq j i (hik.trans hj), C.state_eq j k hj]
    exact (C.history j).increasing i k _ _ hik
  · rw [C.state_top k hk]
    by_cases hi : C.Covered i
    · obtain ⟨j, hj⟩ := hi
      rw [C.state_eq j i hj]
      exact ((C.history j).state_extends_last i hj).trans (C.extends_top j)
    · rw [C.state_top i hi]
      exact extends_refl _

private theorem transition_transport
    {p q p' q' : BasicCondition V I block μ}
    (hp : p = p') (hq : q = q') (t : Transition hμ p q) :
    ∃ s : Transition hμ p' q', HEq s t := by
  subst p'
  subst q'
  exact ⟨t, HEq.rfl⟩

theorem step_exists (i : Ordinal.{u}) (hi : Order.succ i ≤ C.length) :
    ∃ t : Transition hμ (C.state i) (C.state (Order.succ i)),
      ∀ j (hj : Order.succ i ≤ (C.history j).length),
        HEq t ((C.history j).step i hj) := by
  obtain ⟨j, hj⟩ := C.covered_succ i hi
  obtain ⟨t, ht⟩ := transition_transport
    (C.state_eq j i ((Order.le_succ i).trans hj)).symm
    (C.state_eq j (Order.succ i) hj).symm ((C.history j).step i hj)
  exact ⟨t, fun k hk => ht.trans (C.steps_agree j k i hj hk)⟩

noncomputable def step (i : Ordinal.{u}) (hi : Order.succ i ≤ C.length) :
    Transition hμ (C.state i) (C.state (Order.succ i)) :=
  Classical.choose (C.step_exists i hi)

theorem step_heq (j : J) (i : Ordinal.{u})
    (hi : Order.succ i ≤ C.length) (hj : Order.succ i ≤ (C.history j).length) :
    HEq (C.step i hi) ((C.history j).step i hj) :=
  Classical.choose_spec (C.step_exists i hi) j hj

theorem limit_support (i : Ordinal.{u}) (hi : i ≤ C.length)
    (hlim : Order.IsSuccLimit i) (x : V) :
    x ∈ (C.state i).support ↔ ∃ j, ∃ _hji : j < i, x ∈ (C.state j).support := by
  classical
  by_cases hcov : C.Covered i
  · obtain ⟨k, hk⟩ := hcov
    rw [C.state_eq k i hk]
    constructor
    · intro hx
      obtain ⟨j, hji, hjx⟩ := ((C.history k).limit_support i hk hlim x).mp hx
      exact ⟨j, hji, (congrArg (fun p : BasicCondition V I block μ => x ∈ p.support)
        (C.state_eq k j (hji.le.trans hk))).mpr hjx⟩
    · rintro ⟨j, hji, hjx⟩
      apply ((C.history k).limit_support i hk hlim x).mpr
      refine ⟨j, hji, ?_⟩
      exact (congrArg (fun p : BasicCondition V I block μ => x ∈ p.support)
        (C.state_eq k j (hji.le.trans hk))).mp hjx
  · rw [C.state_top i hcov]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      have hki : (C.history k).length < i := lt_of_not_ge (fun h => hcov ⟨k, h⟩)
      refine ⟨(C.history k).length, hki, ?_⟩
      exact (congrArg (fun p : BasicCondition V I block μ => x ∈ p.support)
        (C.state_eq k (C.history k).length le_rfl)).mpr hk
    · rintro ⟨j, hji, hjx⟩
      obtain ⟨k, hk⟩ := C.covered_of_lt j (hji.trans_le hi)
      rw [C.state_eq k j hk] at hjx
      exact Set.mem_iUnion.mpr ⟨k, ((C.history k).state_extends_last j hk).1 hjx⟩

theorem limit_blue (i : Ordinal.{u}) (hi : i ≤ C.length)
    (hlim : Order.IsSuccLimit i) (x y : V) :
    (C.state i).blue x y ↔ ∃ j, ∃ _hji : j < i, (C.state j).blue x y := by
  classical
  by_cases hcov : C.Covered i
  · obtain ⟨k, hk⟩ := hcov
    rw [C.state_eq k i hk]
    constructor
    · intro hxy
      obtain ⟨j, hji, hjxy⟩ := ((C.history k).limit_blue i hk hlim x y).mp hxy
      exact ⟨j, hji, (congrArg (fun p : BasicCondition V I block μ => p.blue x y)
        (C.state_eq k j (hji.le.trans hk))).mpr hjxy⟩
    · rintro ⟨j, hji, hjxy⟩
      apply ((C.history k).limit_blue i hk hlim x y).mpr
      refine ⟨j, hji, ?_⟩
      exact (congrArg (fun p : BasicCondition V I block μ => p.blue x y)
        (C.state_eq k j (hji.le.trans hk))).mp hjxy
  · rw [C.state_top i hcov]
    constructor
    · rintro ⟨k, hk⟩
      have hki : (C.history k).length < i := lt_of_not_ge (fun h => hcov ⟨k, h⟩)
      refine ⟨(C.history k).length, hki, ?_⟩
      exact (congrArg (fun p : BasicCondition V I block μ => p.blue x y)
        (C.state_eq k (C.history k).length le_rfl)).mpr hk
    · rintro ⟨j, hji, hjxy⟩
      obtain ⟨k, hk⟩ := C.covered_of_lt j (hji.trans_le hi)
      rw [C.state_eq k j hk] at hjxy
      obtain ⟨hx, hy⟩ := ((C.history k).state j hk).blue_support hjxy
      exact ⟨k, (((C.history k).state_extends_last j hk).2 x hx y hy).mpr hjxy⟩

/-- The coherent union retains initial nontriviality and actual successor data. -/
noncomputable def limit : History V I block μ hμ where
  length := C.length
  length_lt := C.length_lt
  state i _ := C.state i
  increasing i j _ _ hij := C.state_increasing i j hij
  initial_red := by
    obtain ⟨j, hj⟩ := C.covered_zero
    rw [C.state_eq j 0 hj]
    exact (C.history j).initial_red
  initial_block_injective := by
    obtain ⟨j, hj⟩ := C.covered_zero
    rw [C.state_eq j 0 hj]
    exact (C.history j).initial_block_injective
  initial_nontrivial := by
    obtain ⟨j, hj⟩ := C.covered_zero
    rw [C.state_eq j 0 hj]
    exact (C.history j).initial_nontrivial
  step i hi := C.step i hi
  limit_support i hi hlim x := C.limit_support i hi hlim x
  limit_blue i hi hlim x y := C.limit_blue i hi hlim x y

/-- Every input history is a pure prefix of the union, including its witnesses. -/
theorem pureExtends_limit (j : J) : PureExtends (C.history j) C.limit := by
  refine ⟨C.length_le j, ?_, ?_⟩
  · intro i hi
    exact (C.state_eq j i hi).symm
  · intro i hi
    exact (C.step_heq j i (hi.trans (C.length_le j)) hi).symm

/-- The final support is exactly the union of the input final supports. -/
theorem limit_support_eq : C.limit.last.support = ⋃ j, (C.history j).last.support := by
  apply Set.Subset.antisymm
  · intro x hx
    classical
    by_cases hcov : C.Covered C.length
    · obtain ⟨j, hj⟩ := hcov
      have heq : C.length = (C.history j).length := le_antisymm hj (C.length_le j)
      change x ∈ (C.state C.length).support at hx
      rw [C.state_eq j C.length hj] at hx
      exact Set.mem_iUnion.mpr ⟨j, by simpa only [heq, History.last] using hx⟩
    · change x ∈ (C.state C.length).support at hx
      rw [C.state_top C.length hcov] at hx
      exact hx
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact (C.pureExtends_limit j).last_extends.1 hj

/-- The final blue relation is exactly the union of the input blue relations. -/
theorem limit_blue_iff (x y : V) :
    C.limit.last.blue x y ↔ ∃ j, (C.history j).last.blue x y := by
  constructor
  · intro hxy
    classical
    by_cases hcov : C.Covered C.length
    · obtain ⟨j, hj⟩ := hcov
      have heq : C.length = (C.history j).length := le_antisymm hj (C.length_le j)
      change (C.state C.length).blue x y at hxy
      rw [C.state_eq j C.length hj] at hxy
      exact ⟨j, by simpa only [heq, History.last] using hxy⟩
    · change (C.state C.length).blue x y at hxy
      rw [C.state_top C.length hcov] at hxy
      exact hxy
  · rintro ⟨j, hxy⟩
    obtain ⟨hx, hy⟩ := (C.history j).last.blue_support hxy
    exact ((C.pureExtends_limit j).last_extends.2 x hx y hy).mpr hxy

/-- Existence version of the actual coherent-union construction. -/
theorem exists_pure_upper_bound :
    ∃ K : History V I block μ hμ, K.length = C.length ∧
      (∀ j, PureExtends (C.history j) K) ∧
      K.last.support = ⋃ j, (C.history j).last.support ∧
      ∀ x y, K.last.blue x y ↔ ∃ j, (C.history j).last.blue x y :=
  ⟨C.limit, rfl, C.pureExtends_limit, C.limit_support_eq, C.limit_blue_iff⟩

end PureChain
end Erdos1220.History

#print axioms Erdos1220.History.PureChain.exists_pure_upper_bound
