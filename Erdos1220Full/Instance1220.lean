import Erdos1220Full.WitnessSetup
import Erdos1220Full.GenericColouring
import Erdos1220Full.GlueCAlg

/-!
# The concrete forcing instance for `λ = ℶ_{𝔠⁺}`

`X := card_ex λ` (an ordinal `PSet`), vertices `X.Type = Vtx`, blocks `Blk`, `μ := 𝔠⁺`.
This file fixes the concrete algebra `𝔹₁ := CAlg Vtx Blk block μ _ : Type`, proves it is
nontrivial (a covering initial history exists), and records the generic colouring facts on it.
-/

open Cardinal Flypitch bSet Lattice
open Erdos1220.Witness Erdos1220Full.HistoryForcing Erdos1220Full.GenericColouring

namespace Erdos1220.Final

/-- The ground ordinal `PSet` of `λ`. -/
noncomputable abbrev X : PSet.{0} := PSet.card_ex bethWitness.{0}

/-- `X.Type` is the vertex type (propositionally). -/
noncomputable def eX : X.Type ≃ Vtx.{0} := Equiv.cast PSet.ordinalMk_type

/-- The block map on `X.Type`. -/
noncomputable def blockX (v : X.Type) : Blk.{0} := block (eX v)

/-- Block representatives in `X.Type`. -/
noncomputable def repX (i : Blk.{0}) : X.Type := eX.symm (rep i)

theorem blockX_repX (i : Blk.{0}) : blockX (repX i) = i := by
  simp [blockX, repX, block_rep]

/-- `μ = 𝔠⁺`. -/
noncomputable abbrev μ₁ : Cardinal.{0} := Order.succ Cardinal.continuum

theorem hμ₁ : ℵ₀ ≤ μ₁ := aleph0_le_continuum.trans (Order.le_succ _)

theorem mk_Blk_le : #Blk.{0} ≤ μ₁ := mk_Blk.le

instance : Nontrivial Blk.{0} := by
  rw [← Cardinal.one_lt_iff_nontrivial, mk_Blk]
  exact (one_lt_aleph0.trans_le aleph0_le_continuum).trans_le (Order.le_succ _)

instance instNonempty : Nonempty (CHP0 X.Type Blk.{0} blockX μ₁ hμ₁) :=
  nonemptyC repX blockX_repX mk_Blk_le

/-- The concrete Boolean algebra. -/
abbrev 𝔹₁ : Type := CAlg X.Type Blk.{0} blockX μ₁ hμ₁

theorem X_inj : ∀ i j, PSet.Equiv (X.Func i) (X.Func j) → i = j := by
  intro i j h
  by_contra hij
  exact PSet.ordinalMk_inj _ i j hij h

/-- The generic colouring name on the concrete algebra. -/
noncomputable abbrev cdot₁ : bSet 𝔹₁ := cdot X blockX μ₁ hμ₁

theorem colouring₁ : (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.colouring (check X) cdot₁ :=
  colouring_cdot X_inj

theorem distrib₁ : Erdos1220Full.CardB.DistribHyp μ₁ 𝔹₁ := distribHyp_CAlg

end Erdos1220.Final

#print axioms Erdos1220.Final.colouring₁
#print axioms Erdos1220.Final.distrib₁
