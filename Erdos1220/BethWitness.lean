import Erdos1220

/-!
# A strong-limit ground-model candidate

The singular cardinal `beth_(continuum⁺)` satisfies all hypotheses of problem
1220 without the deep Shelah cardinal-arithmetic input used for
`aleph_(continuum⁺)`. This prepares a preservation-based forcing route.

This module does not assert a negative partition relation for this cardinal.
Its ground-model strong-limit property must not be asserted to persist after
the proposed forcing. The countable-power and cofinality properties are the
ones that would have to be preserved by a separate forcing argument.
-/

open Cardinal Order

universe u

namespace Erdos1220

theorem isOmegaInaccessible_of_isStrongLimit {κ : Cardinal.{u}}
    (hκ : κ.IsStrongLimit) (hω : ℵ₀ < κ) : IsOmegaInaccessible κ := by
  intro μ hμ
  let ν := max μ ℵ₀
  have hν : ν < κ := max_lt hμ hω
  have hων : ℵ₀ ≤ ν := le_max_right _ _
  have hν0 : ν ≠ 0 := ne_of_gt (Cardinal.aleph0_pos.trans_le hων)
  calc
    μ ^ ℵ₀ ≤ ν ^ ℵ₀ := Cardinal.power_le_power_right (le_max_left _ _)
    _ ≤ ν ^ ν := Cardinal.power_le_power_left hν0 hων
    _ = 2 ^ ν := Cardinal.power_self_eq hων
    _ < κ := hκ.2 hν

theorem isNormal_beth_ord :
    Order.IsNormal (fun α : Ordinal.{u} => (Cardinal.beth α).ord) := by
  rw [Order.isNormal_iff]
  refine ⟨Cardinal.ord_strictMono.comp Cardinal.beth_strictMono, ?_⟩
  intro α hα β hβ
  apply Cardinal.ord_le.mpr
  apply (Cardinal.isNormal_beth.le_iff_forall_le hα).mpr
  intro γ hγ
  exact Cardinal.ord_le.mp (hβ γ hγ)

noncomputable def bethWitness : Cardinal.{u} :=
  Cardinal.beth (Order.succ (Cardinal.continuum : Cardinal.{u})).ord

theorem bethWitness_isStrongLimit : bethWitness.{u}.IsStrongLimit := by
  exact Cardinal.isStrongLimit_beth.mpr
    succ_continuum_ord_isSuccLimit.isSuccPrelimit

theorem succ_continuum_lt_bethWitness :
    Order.succ (Cardinal.continuum : Cardinal.{u}) < bethWitness.{u} := by
  have hlim : Order.IsSuccLimit bethWitness.{u} :=
    bethWitness_isStrongLimit.isSuccLimit
  exact lt_of_le_of_ne (Cardinal.le_beth_ord _) (hlim.succ_ne _)

theorem cof_bethWitness :
    bethWitness.{u}.ord.cof = Order.succ (Cardinal.continuum : Cardinal.{u}) := by
  unfold bethWitness
  rw [Ordinal.cof_map_of_isNormal isNormal_beth_ord succ_continuum_ord_isSuccLimit]
  exact (Cardinal.isRegular_succ Cardinal.aleph0_le_continuum).cof_ord

theorem bethWitness_isSingular : bethWitness.{u}.IsSingular := by
  constructor
  · exact Cardinal.aleph0_le_beth _
  · rw [cof_bethWitness]
    exact ne_of_lt succ_continuum_lt_bethWitness

/-- All original hypotheses hold for the proposed ground-model cardinal.
There are no external theorem parameters in this statement. -/
theorem bethWitness_hypotheses : Hypotheses bethWitness.{u} := by
  refine ⟨bethWitness_isSingular, ?_, ?_⟩
  · apply isOmegaInaccessible_of_isStrongLimit bethWitness_isStrongLimit
    exact (Cardinal.aleph0_le_continuum.trans (Order.le_succ _)).trans_lt
      succ_continuum_lt_bethWitness
  · rw [cof_bethWitness]
    exact succ_continuum_isOmegaInaccessible

end Erdos1220

#print axioms Erdos1220.bethWitness_hypotheses
