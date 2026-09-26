import Erdos1220Full.Instance1220
import Erdos1220Full.CAlgChain
import Erdos1220Full.BlueExclusion

/-!
# Chain condition and blue exclusion for the concrete instance

* `cc₁ : ChainCondition (Order.succ (2 ^ μ₁)) 𝔹₁`;
* `blue₁`: the second disjunct of `Sem.arrow (check X) cdot₁` is refuted by
  every `w, H`.
-/

open Cardinal Flypitch bSet Lattice
open Erdos1220.Witness Erdos1220Full.HistoryForcing Erdos1220Full.GenericColouring

namespace Erdos1220.Final

/-- The `(2^μ₁)⁺`-chain condition of the concrete algebra. -/
theorem cc₁ : Erdos1220Full.ChainCondition (Order.succ (2 ^ μ₁)) 𝔹₁ :=
  chainCondition_CAlg_two_pow (mk_Blk_le.trans (Cardinal.cantor μ₁).le)

/-- Distinct members of `X` are `∈`-comparable. -/
theorem X_ord : ∀ i j, i ≠ j → X.Func i ∈ X.Func j ∨ X.Func j ∈ X.Func i := by
  intro i j hij
  have hX : PSet.Ord X := PSet.Ord_mk _
  have hi : PSet.Ord (X.Func i) := PSet.Ord_of_mem_Ord' (PSet.func_mem X i) hX
  have hj : PSet.Ord (X.Func j) := PSet.Ord_of_mem_Ord' (PSet.func_mem X j) hX
  rcases PSet.Ord.trichotomy hi hj with h | h | h
  · exact absurd (X_inj i j h) hij
  · exact Or.inl h
  · exact Or.inr h

theorem aleph_one_le_μ₁ : Cardinal.aleph 1 ≤ μ₁ :=
  Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)

/-- **No uncountable blue-homogeneous subset of `X̌` in `V 𝔹₁`.** -/
theorem blue₁ (w H : bSet 𝔹₁) :
    Flypitch.Erdos1220.Sem.omega1 w ⊓ (Flypitch.Erdos1220.Sem.subset H (check X) ⊓
      (Flypitch.Erdos1220.Sem.eqCard H w ⊓ Flypitch.Erdos1220.Sem.homog1 cdot₁ H)) ≤ ⊥ :=
  omega1_homog_le_bot X_inj X_ord aleph_one_le_μ₁ w H

end Erdos1220.Final

#print axioms Erdos1220.Final.cc₁
#print axioms Erdos1220.Final.X_ord
#print axioms Erdos1220.Final.blue₁
