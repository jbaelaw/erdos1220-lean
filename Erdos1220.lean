import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Data.Finset.Card

/-!
# Applying an external counterexample to Erdős problem 1220

This file formalizes elementary cardinal calculations and a conditional
application of an external partition counterexample. It does not formalize
forcing, the consistency of ZFC, or the Shelah–Stanley construction.

The Shelah bound and the negative partition relation are explicit theorem
parameters. Neither is introduced as a global axiom or asserted without proof.
In particular, a relative-consistency theorem is NOT replaced by an
unconditional negative partition relation in Lean's ambient universe.

Sources:
* https://www.erdosproblems.com/1220
* Shelah–Stanley, Ann. Pure Appl. Logic 36 (1987), 119–152,
  Theorem 3 and p. 125, https://shelah.logic.at/files/95472/258.pdf

Checked with Lean 4.33.1 and mathlib v4.33.1 on Linux.
See validation.json and the saved compiler log for the exact scope and revision.
-/

open Cardinal Order

universe u

namespace Erdos1220

/-- Closure below `κ` under taking countable cardinal powers. -/
def IsOmegaInaccessible (κ : Cardinal.{u}) : Prop :=
  ∀ μ : Cardinal.{u}, μ < κ → μ ^ ℵ₀ < κ

/-- The asymmetric binary partition arrow `κ → (α, β)²`.

The coloring is defined on unordered two-element subsets. The two alternatives
have the indicated exact cardinalities, and every pair inside the witness has
the specified color. This is the binary specialization of the formulation used
in FormalConjecturesForMathlib's `cardinalPartitionRel`.
-/
def PairArrow (κ α β : Cardinal.{u}) : Prop :=
  ∀ (V : Type u), #V = κ →
    ∀ color : {e : Finset V // e.card = 2} → Bool,
      (∃ H : Set V, #H = α ∧
        ∀ (e : Finset V) (he : e.card = 2),
          (↑e : Set V) ⊆ H → color ⟨e, he⟩ = false) ∨
      (∃ H : Set V, #H = β ∧
        ∀ (e : Finset V) (he : e.card = 2),
          (↑e : Set V) ⊆ H → color ⟨e, he⟩ = true)

/-- All hypotheses in the website's formulation. -/
def Hypotheses (κ : Cardinal.{u}) : Prop :=
  κ.IsSingular ∧ IsOmegaInaccessible κ ∧ IsOmegaInaccessible κ.ord.cof

/-- The universal positive assertion, in one fixed universe. -/
def Problem1220 : Prop :=
  ∀ κ : Cardinal.{u}, Hypotheses κ → PairArrow κ κ ℵ₁

/-- The cardinal `ℵ_(𝔠⁺)`, with the index explicitly converted to an ordinal. -/
noncomputable def lambdaStar : Cardinal.{u} :=
  Cardinal.aleph (Order.succ (Cardinal.continuum : Cardinal.{u})).ord

theorem succ_continuum_isOmegaInaccessible :
    IsOmegaInaccessible (Order.succ (Cardinal.continuum : Cardinal.{u})) := by
  intro μ hμ
  have hμc : μ ≤ (𝔠 : Cardinal.{u}) := Order.lt_succ_iff.mp hμ
  calc
    μ ^ ℵ₀ ≤ (𝔠 : Cardinal.{u}) ^ ℵ₀ := Cardinal.power_le_power_right hμc
    _ = 𝔠 := Cardinal.continuum_power_aleph0
    _ < Order.succ 𝔠 := Order.lt_succ _

theorem succ_continuum_ord_isSuccLimit :
    Order.IsSuccLimit (Order.succ (Cardinal.continuum : Cardinal.{u})).ord := by
  apply Cardinal.isSuccLimit_ord
  exact Cardinal.aleph0_le_continuum.trans (Order.le_succ _)

theorem cof_lambdaStar :
    lambdaStar.{u}.ord.cof = Order.succ (Cardinal.continuum : Cardinal.{u}) := by
  unfold lambdaStar
  rw [Cardinal.ord_aleph, Ordinal.cof_omega succ_continuum_ord_isSuccLimit]
  exact (Cardinal.isRegular_succ Cardinal.aleph0_le_continuum).cof_ord

theorem succ_continuum_lt_lambdaStar :
    Order.succ (Cardinal.continuum : Cardinal.{u}) < lambdaStar.{u} := by
  have hlim : Order.IsSuccLimit lambdaStar.{u} :=
    Cardinal.isNormal_aleph.map_isSuccLimit succ_continuum_ord_isSuccLimit
  exact lt_of_le_of_ne (Cardinal.le_aleph_ord _) (hlim.succ_ne _)

theorem lambdaStar_isSingular : lambdaStar.{u}.IsSingular := by
  constructor
  · exact Cardinal.aleph0_le_aleph _
  · rw [cof_lambdaStar]
    exact ne_of_lt succ_continuum_lt_lambdaStar

theorem cof_lambdaStar_isOmegaInaccessible :
    IsOmegaInaccessible lambdaStar.{u}.ord.cof := by
  rw [cof_lambdaStar]
  exact succ_continuum_isOmegaInaccessible

/-- Only the deep cardinal-arithmetic bound is an external input here. -/
theorem lambdaStar_hypotheses
    (shelahBound : IsOmegaInaccessible lambdaStar.{u}) :
    Hypotheses lambdaStar.{u} := by
  exact ⟨lambdaStar_isSingular, shelahBound, cof_lambdaStar_isOmegaInaccessible⟩

/-- Inside any ambient interpretation satisfying both external inputs,
the universal assertion has a counterexample. This is a conditional implication,
not a formal proof that such a model of ZFC exists. -/
theorem not_problem1220_of_negative_partition
    (shelahBound : IsOmegaInaccessible lambdaStar.{u})
    (negativePartition : ¬ PairArrow lambdaStar.{u} lambdaStar.{u} ℵ₁) :
    ¬ Problem1220.{u} := by
  intro positive
  exact negativePartition (positive lambdaStar (lambdaStar_hypotheses shelahBound))

end Erdos1220

#print axioms Erdos1220.succ_continuum_isOmegaInaccessible
#print axioms Erdos1220.cof_lambdaStar
#print axioms Erdos1220.lambdaStar_isSingular
#print axioms Erdos1220.not_problem1220_of_negative_partition
