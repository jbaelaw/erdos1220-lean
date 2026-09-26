import Erdos1220Full.CoverForcing
import Erdos1220Full.AntichainHP

/-!
# The `(2^μ)⁺`-chain condition of the covering algebra

A common weak extension of two covering histories covers again, so the
`(2^μ)⁺`-antichain bound of `HP` (`antichainBound_HP`) restricts to the
covering forcing `CHP`, and `chainCondition_CAlg` applies.
-/

open Cardinal Set Order

universe u

namespace Erdos1220Full

namespace HistoryForcing

open Erdos1220 Erdos1220.BasicCondition Erdos1220.BPHistory

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

theorem chainCondition_CAlg_two_pow [Nonempty (CHP0 V I block μ hμ)] (hI : #I ≤ 2 ^ μ) :
    ChainCondition (Order.succ (2 ^ μ)) (CAlg V I block μ hμ) := by
  apply chainCondition_CAlg
  intro ι p hι
  obtain ⟨i, j, hij, r, hri, hrj⟩ := antichainBound_HP (hμ := hμ) (block := block) hI
    (ULift.{u + 1} ι) (fun k => (show HP V I block μ hμ from (p k.down).1))
    (by rw [Cardinal.mk_uLift]; exact Cardinal.lift_le.mpr hι)
  have hcov : CoversBlocks (show BPHistory V I block μ hμ from r).1.last :=
    (HistoryForcing.le_iff.mp hri).coversBlocks (p i.down).2
  exact ⟨i.down, j.down, fun h => hij (ULift.down_injective h),
    ⟨⟨r, hcov⟩, HistoryForcing.le_iff.mp hri, HistoryForcing.le_iff.mp hrj⟩⟩

end HistoryForcing

end Erdos1220Full

#print axioms Erdos1220Full.HistoryForcing.chainCondition_CAlg_two_pow
