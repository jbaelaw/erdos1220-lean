import Erdos1220.BlockPreserving
import Erdos1220.HistoryConstruction
import Erdos1220.HistoryLimit

/-!
# Pure closure preserves actual block labels

The global block-label invariant is inherited by pure prefixes, admissible
successor append, and the bounded coherent limits of `HistoryLimit`. This is
an invariant-preservation result, not a chain condition or forcing density
claim.
-/

open Cardinal Set Order

universe u v

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- Block preservation is invariant under transport of the entire recorded
transition, including its source and result. -/
theorem transition_preservesBlocks_iff_of_heq
    {p r p' r' : BasicCondition V I block μ}
    (hp : p = p') (hr : r = r')
    {t : Transition hμ p r} {t' : Transition hμ p' r'} (ht : HEq t t') :
    t.iso.PreservesBlocks ↔ t'.iso.PreservesBlocks := by
  subst p'
  subst r'
  cases ht
  rfl

theorem PureExtends.blockPreserving {H K : History V I block μ hμ}
    (h : PureExtends H K) (hK : K.BlockPreserving) : H.BlockPreserving := by
  intro i hi
  exact (transition_preservesBlocks_iff_of_heq
    (h.state_eq i ((Order.le_succ i).trans hi))
    (h.state_eq (Order.succ i) hi) (h.step_heq i hi)).mpr
      (hK i (hi.trans h.length_le))

private theorem mpr_heq {α β : Sort v} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  exact HEq.rfl

/-- Appending a label-preserving transition preserves the invariant. -/
theorem BlockPreserving.append {H : History V I block μ hμ}
    (hH : H.BlockPreserving) (r : BasicCondition V I block μ)
    (t : Transition hμ H.last r) (ht : t.iso.PreservesBlocks) :
    (H.append r t).BlockPreserving := by
  intro i hi
  have hiold : i ≤ H.length := Order.succ_le_succ_iff.mp hi
  by_cases heq : i = H.length
  · subst i
    have hs : HEq ((H.append r t).step H.length hi) t := by
      simp only [History.append, eq_self, dite_true]
      exact mpr_heq _ _
    exact (transition_preservesBlocks_iff_of_heq
      (H.append_preserves_state r t H.length le_rfl)
      (H.append_last r t) hs).mpr ht
  · have hisucc : Order.succ i ≤ H.length :=
      Order.succ_le_of_lt (lt_of_le_of_ne hiold heq)
    have hs : HEq ((H.append r t).step i hi) (H.step i hisucc) := by
      simp only [History.append, dite_eq_right heq, mpr_heq]
    exact (transition_preservesBlocks_iff_of_heq
      (H.append_preserves_state r t i hiold)
      (H.append_preserves_state r t (Order.succ i) hisucc) hs).mpr (hH i hisucc)

namespace PureChain

variable {J : Type u} [LinearOrder J] [Nonempty J]
variable (C : PureChain (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ) J)

/-- Every successor transition of the coherent union is inherited from one
of the original histories, so its block-label invariant is preserved. -/
theorem limit_blockPreserving (hC : ∀ j, (C.history j).BlockPreserving) :
    C.limit.BlockPreserving := by
  intro i hi
  obtain ⟨j, hj⟩ := C.covered_succ i hi
  exact (transition_preservesBlocks_iff_of_heq
    (C.state_eq j i ((Order.le_succ i).trans hj))
    (C.state_eq j (Order.succ i) hj) (C.step_heq j i hi hj)).mpr (hC j i hj)

end PureChain
end Erdos1220.History

#print axioms Erdos1220.History.PureExtends.blockPreserving
#print axioms Erdos1220.History.BlockPreserving.append
#print axioms Erdos1220.History.PureChain.limit_blockPreserving
