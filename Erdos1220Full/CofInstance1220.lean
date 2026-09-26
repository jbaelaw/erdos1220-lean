import Erdos1220Full.CofClause
import Erdos1220Full.HypInstance1220

/-!
# The cofinality clause on the concrete algebra `𝔹₁`

`X = card_ex ℶ_{𝔠⁺}`, `κ = μ₁ = 𝔠⁺ = cf λ`. The abstract `sem_cof_clause`
(`CofClause.lean`) is instantiated with `distrib₁`, and with the `κ̌` facts
`cardinal_κ₁`, `omegaInacc_κ₁`, `cofinal_κ₁` of `HypInstance1220.lean`.
-/

open Cardinal Flypitch bSet Lattice
open Erdos1220.Witness

namespace Erdos1220.Final

/-- **The cofinality clause of `Sem.hyp (check X)` on `𝔹₁`.** -/
theorem cof₁ : (⊤ : 𝔹₁) ≤ ⨅ d : bSet 𝔹₁, Flypitch.Erdos1220.Sem.cof (check X) d ⟹
    Flypitch.Erdos1220.Sem.omegaInacc d := by
  obtain ⟨Sg, h1, h2, h3⟩ := cofinal_κ₁
  exact Erdos1220Full.CardB.sem_cof_clause distrib₁ (κ := μ₁) (lo := bethWitness.{0}.ord)
    (fun ρ ho => ⟨(Cardinal.lt_ord.1 ho).le, by rw [cof_bethWitness]; exact Cardinal.lt_ord.1 ho⟩)
    cardinal_κ₁ omegaInacc_κ₁ (check Sg) h1 h2 h3

/-- **`⊤ ≤ Sem.hyp λ̌` on `𝔹₁`.** -/
theorem hyp₁ : (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.hyp (check X) :=
  hyp₁_of_cofClause cof₁

end Erdos1220.Final

#print axioms Erdos1220.Final.cof₁
#print axioms Erdos1220.Final.hyp₁
