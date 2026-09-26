import Erdos1220Full.CoverForcing
import Erdos1220Full.CardPreserve

/-!
# `DistribHyp μ` for the covering history algebra

Agent-A's abstract distributivity hypothesis `CardB.DistribHyp` holds for `CAlg`, by the
strategic-closure distributivity `exists_forall_of_card_leC`.
-/

open Cardinal Flypitch bSet Lattice

universe u

namespace Erdos1220Full.HistoryForcing

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}
variable [Nonempty (CHP0 V I block μ hμ)]

theorem distribHyp_CAlg : CardB.DistribHyp μ (CAlg V I block μ hμ) := by
  intro J hJ ι φ Γ hΓ h
  obtain ⟨q, c, hq, hc⟩ := exists_forall_of_card_leC (J := J)
    (by simpa using hJ) hΓ φ
    (fun j Γ' hΓ' hle => nonzero_inf_of_nonzero_le_supr hΓ' (hle.trans (h j)))
  exact ⟨emb q, emb_pos q, hq, c, hc⟩

end Erdos1220Full.HistoryForcing

#print axioms Erdos1220Full.HistoryForcing.distribHyp_CAlg
