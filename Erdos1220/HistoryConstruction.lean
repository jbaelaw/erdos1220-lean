import Erdos1220.History
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Initial histories and successor extension

The history type is inhabited when two different blocks are available, and
every admissible recorded amalgamation can actually be appended. The length bound, all old states, and limit continuity
are preserved. This is a pure successor construction, not yet strategic
closure of the full forcing order.
-/

open Cardinal Set Order

universe u

namespace Erdos1220

namespace BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}

def twoPoint (hμ : ℵ₀ ≤ μ) (x y : V) : BasicCondition V I block μ where
  support := {x, y}
  blue _ _ := False
  symmetric := False.elim
  irreflexive := fun _ => id
  blue_support := False.elim
  different_blocks := False.elim
  small := (Cardinal.le_aleph0_iff_set_countable.mpr
    ((Set.countable_singleton y).insert x)).trans hμ

end BasicCondition

open BasicCondition

namespace History

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

def ofInitial (p : BasicCondition V I block μ) (hred : ∀ x y, ¬ p.blue x y)
    (hinj : ∀ x ∈ p.support, ∀ y ∈ p.support, block x = block y → x = y)
    (hnontrivial : ∃ x ∈ p.support, ∃ y ∈ p.support, x ≠ y) :
    History V I block μ hμ where
  length := 0
  length_lt := (Cardinal.isRegular_succ hμ).ord_pos
  state _ _ := p
  increasing _ _ _ _ _ := extends_refl p
  initial_red := hred
  initial_block_injective := hinj
  initial_nontrivial := hnontrivial
  step i hi := False.elim ((Order.lt_succ i).not_ge (hi.trans bot_le))
  limit_support i hi hlim _ := by
    have hi0 : i = 0 := le_antisymm hi bot_le
    have : False := by simp [hi0] at hlim
    exact False.elim this
  limit_blue i hi hlim _ _ := by
    have hi0 : i = 0 := le_antisymm hi bot_le
    have : False := by simp [hi0] at hlim
    exact False.elim this

def ofTwoPoints (x y : V) (hxy : block x ≠ block y) : History V I block μ hμ := by
  refine ofInitial (BasicCondition.twoPoint hμ x y) (fun _ _ => id) ?_ ?_
  · intro a ha b hb hab
    change a ∈ ({x, y} : Set V) at ha
    change b ∈ ({x, y} : Set V) at hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact False.elim (hxy hab)
    · exact False.elim (hxy hab.symm)
    · rfl
  · exact ⟨x, by simp [BasicCondition.twoPoint], y, by simp [BasicCondition.twoPoint],
      fun h => hxy (congrArg block h)⟩

theorem histories_nonempty_of_two_blocks (x y : V) (hxy : block x ≠ block y) :
    Nonempty (History V I block μ hμ) := ⟨ofTwoPoints x y hxy⟩

open scoped Classical in
noncomputable def appendedState (H : History V I block μ hμ)
    (r : BasicCondition V I block μ) (i : Ordinal.{u}) : BasicCondition V I block μ :=
  if hi : i ≤ H.length then H.state i hi else r

theorem appendedState_old (H : History V I block μ hμ) (r : BasicCondition V I block μ)
    (i : Ordinal.{u}) (hi : i ≤ H.length) : H.appendedState r i = H.state i hi := by
  simp only [appendedState, dite_eq_left hi]

theorem appendedState_new (H : History V I block μ hμ) (r : BasicCondition V I block μ) :
    H.appendedState r (Order.succ H.length) = r := by
  simp only [appendedState, dite_eq_right (Order.lt_succ H.length).not_ge]

theorem old_of_limit_le_succ (H : History V I block μ hμ) (i : Ordinal.{u})
    (hi : i ≤ Order.succ H.length) (hlim : Order.IsSuccLimit i) : i ≤ H.length := by
  by_contra hold
  have heq : i = Order.succ H.length :=
    le_antisymm hi (Order.succ_le_of_lt (lt_of_not_ge hold))
  exact (hlim.succ_ne H.length) heq.symm

open scoped Classical in
/-- Append the actual recorded amalgamation, preserving the whole prefix. -/
noncomputable def append (H : History V I block μ hμ) (r : BasicCondition V I block μ)
    (t : Transition hμ H.last r) : History V I block μ hμ where
  length := Order.succ H.length
  length_lt :=
    (Cardinal.isSuccLimit_ord (hμ.trans (Order.le_succ μ))).succ_lt H.length_lt
  state i _ := H.appendedState r i
  increasing i j _ _ hij := by
    by_cases hj : j ≤ H.length
    · have hi := hij.trans hj
      rw [H.appendedState_old r i hi, H.appendedState_old r j hj]
      exact H.increasing i j hi hj hij
    · simp only [appendedState, dite_eq_right hj]
      by_cases hi : i ≤ H.length
      · rw [dite_eq_left hi]
        exact (H.state_extends_last i hi).trans t.extends_left
      · rw [dite_eq_right hi]
        exact extends_refl r
  initial_red := by
    simpa only [appendedState, dite_eq_left (show (0 : Ordinal.{u}) ≤ H.length from bot_le)]
      using H.initial_red
  initial_block_injective := by
    simpa only [appendedState, dite_eq_left (show (0 : Ordinal.{u}) ≤ H.length from bot_le)]
      using H.initial_block_injective
  initial_nontrivial := by
    simpa only [appendedState, dite_eq_left (show (0 : Ordinal.{u}) ≤ H.length from bot_le)]
      using H.initial_nontrivial
  step i hi := by
    have hiold : i ≤ H.length := Order.succ_le_succ_iff.mp hi
    by_cases heq : i = H.length
    · subst i
      simpa only [History.last, H.appendedState_old r H.length le_rfl, H.appendedState_new r]
        using t
    · have hisucc : Order.succ i ≤ H.length :=
        Order.succ_le_of_lt (lt_of_le_of_ne hiold heq)
      simpa only [H.appendedState_old r i hiold, H.appendedState_old r _ hisucc]
        using H.step i hisucc
  limit_support i hi hlim x := by
    have hold := H.old_of_limit_le_succ i hi hlim
    rw [H.appendedState_old r i hold]
    constructor
    · intro hx
      obtain ⟨j, hji, hjx⟩ := (H.limit_support i hold hlim x).mp hx
      refine ⟨j, hji, ?_⟩
      simpa only [H.appendedState_old r j (hji.le.trans hold)] using hjx
    · rintro ⟨j, hji, hjx⟩
      apply (H.limit_support i hold hlim x).mpr
      refine ⟨j, hji, ?_⟩
      simpa only [H.appendedState_old r j (hji.le.trans hold)] using hjx
  limit_blue i hi hlim x y := by
    have hold := H.old_of_limit_le_succ i hi hlim
    rw [H.appendedState_old r i hold]
    constructor
    · intro hxy
      obtain ⟨j, hji, hjxy⟩ := (H.limit_blue i hold hlim x y).mp hxy
      refine ⟨j, hji, ?_⟩
      simpa only [H.appendedState_old r j (hji.le.trans hold)] using hjxy
    · rintro ⟨j, hji, hjxy⟩
      apply (H.limit_blue i hold hlim x y).mpr
      refine ⟨j, hji, ?_⟩
      simpa only [H.appendedState_old r j (hji.le.trans hold)] using hjxy

theorem append_last (H : History V I block μ hμ) (r : BasicCondition V I block μ)
    (t : Transition hμ H.last r) : (H.append r t).last = r :=
  H.appendedState_new r

theorem append_preserves_state (H : History V I block μ hμ)
    (r : BasicCondition V I block μ) (t : Transition hμ H.last r)
    (i : Ordinal.{u}) (hi : i ≤ H.length) :
    (H.append r t).state i (hi.trans (Order.le_succ H.length)) = H.state i hi :=
  H.appendedState_old r i hi

end History
end Erdos1220

#print axioms Erdos1220.History.histories_nonempty_of_two_blocks
#print axioms Erdos1220.History.append_last
#print axioms Erdos1220.History.append_preserves_state
