/-
# Erdős #1220 — `Sem.hyp (check X)` on the concrete algebra `𝔹₁`

Instantiates the abstract lemmas of `HypForced.lean` on `𝔹₁ = CAlg X.Type Blk blockX μ₁ hμ₁`
(`Instance1220.lean`), `X = card_ex ℶ_{𝔠⁺}`, `μ₁ = 𝔠⁺`:

* (Hcc)  `ChainCondition (succ (2 ^ μ₁)) 𝔹₁` (`chainCondition_CAlg_two_pow`), `succ (2^μ₁) ≤ λ`
  since `λ` is a strong limit — used for `Sem.cardinal λ̌`;
* (Hdist) `DistribHyp μ₁ 𝔹₁` (`distrib₁`), `cf λ = μ₁` — used for `Sem.singular λ̌` and `Sem.cardinal κ̌`;
* (HF) countable closure (`check_functions_eq_CAlg` with domain `ω`) — for `Sem.omegaInacc`.

The cofinality clause `⨅ d, Sem.cof λ̌ d ⟹ Sem.omegaInacc d` is taken as a hypothesis
(`CofClause`), to be discharged by `CofClause.lean`; the `κ̌` facts it needs are provided here.
-/
import Erdos1220Full.Instance1220
import Erdos1220Full.HypForced
import Erdos1220Full.CAlgChain

open Cardinal Flypitch bSet Lattice
open Erdos1220.Witness Erdos1220Full.HistoryForcing

namespace Erdos1220.Final

open Flypitch.Erdos1220.Hyp

/-- (HF) on `𝔹₁`: `ω`-sequences into ground ordinals are ground. -/
theorem HF₁ : HF 𝔹₁ := by
  intro o
  have hω : #PSet.omega.{0}.Type ≤ μ₁ := by
    show #(ULift.{0} ℕ) ≤ μ₁
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact hμ₁
  exact check_functions_eq_CAlg (x := PSet.omega) (y := PSet.ordinalMk o) omega_func_inj hω ⊤

/-- (Hcc) on `𝔹₁`. -/
theorem ccHyp₁ : Erdos1220Full.ChainCondition (Order.succ ((2 : Cardinal.{0}) ^ μ₁)) 𝔹₁ :=
  chainCondition_CAlg_two_pow (by rw [mk_Blk]; exact (Cardinal.cantor _).le)

theorem θHyp₁_regular : Cardinal.IsRegular (Order.succ ((2 : Cardinal.{0}) ^ μ₁)) :=
  Cardinal.isRegular_succ (Cardinal.aleph0_le_continuum.trans
    ((Order.le_succ _).trans (Cardinal.cantor _).le))

theorem θHyp₁_le : Order.succ ((2 : Cardinal.{0}) ^ μ₁) ≤ bethWitness.{0} :=
  Order.succ_le_of_lt (Cardinal.IsStrongLimit.two_power_lt bethWitness_isStrongLimit
    succ_continuum_lt_bethWitness)

/-- **`⊤ ≤ Sem.hyp λ̌` on `𝔹₁`, given the cofinality clause.** -/
theorem hyp₁_of_cofClause (hclause : CofClause 𝔹₁ (check X)) :
    (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.hyp (check X) :=
  hyp_of_cofClause ccHyp₁ θHyp₁_regular distrib₁ HF₁ bethWitness_hypotheses θHyp₁_le
    (le_of_eq cof_bethWitness) hclause

/-- The three unconditional clauses of `Sem.hyp λ̌` on `𝔹₁`. -/
theorem cardinal₁ : (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.cardinal (check X) :=
  Erdos1220Full.CardB.sem_cardinal_card_ex_of_chainCondition ccHyp₁ θHyp₁_regular θHyp₁_le

theorem singular₁ : (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.singular (check X) :=
  singular_card_ex_of_distrib distrib₁ bethWitness_isSingular (le_of_eq cof_bethWitness)

theorem omegaInacc₁ : (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.omegaInacc (check X) :=
  omegaInacc_card_ex HF₁ bethWitness_hypotheses.2.1

/-! ### The `κ̌ = (𝔠⁺)ˇ` facts for the cofinality clause -/

/-- `κ̌ = (𝔠⁺)ˇ` is a cardinal in `V 𝔹₁` (Hdist). -/
theorem cardinal_κ₁ : (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.cardinal (check (PSet.card_ex μ₁)) :=
  cardinal_cof_check distrib₁ fun _ ho => (Cardinal.lt_ord.1 ho).le

/-- `κ̌ = (𝔠⁺)ˇ` is `ℵ₀`-inaccessible in `V 𝔹₁` (HF). -/
theorem omegaInacc_κ₁ : (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.omegaInacc (check (PSet.card_ex μ₁)) :=
  omegaInacc_card_ex HF₁ succ_continuum_isOmegaInaccessible

/-- A ground cofinal check-set `Š ⊆ λ̌` with `|Š| = |κ̌|` in `V 𝔹₁`. -/
theorem cofinal_κ₁ : ∃ Sg : PSet.{0},
    (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.subset (check Sg) (check X) ∧
    (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.cofinal (check Sg) (check X) ∧
    (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.eqCard (check Sg) (check (PSet.card_ex μ₁)) := by
  have h := exists_check_cofinal_eqCard (β := 𝔹₁) bethWitness.{0}
  rw [cof_bethWitness] at h
  exact h

/-- The (Hcof)-form: if the cofinality of `λ̌` in `V 𝔹₁` is `κ̌`, then `⊤ ≤ Sem.hyp λ̌`. -/
theorem hyp₁_of_HCof (hcof : HCof 𝔹₁ bethWitness.{0}) :
    (⊤ : 𝔹₁) ≤ Flypitch.Erdos1220.Sem.hyp (check X) :=
  hyp₁_of_cofClause (cofClause_of_HCof HF₁ bethWitness_hypotheses.2.2 hcof)

end Erdos1220.Final

#print axioms Erdos1220.Final.HF₁
#print axioms Erdos1220.Final.ccHyp₁
#print axioms Erdos1220.Final.hyp₁_of_cofClause
#print axioms Erdos1220.Final.cardinal₁
#print axioms Erdos1220.Final.singular₁
#print axioms Erdos1220.Final.omegaInacc₁
#print axioms Erdos1220.Final.cardinal_κ₁
#print axioms Erdos1220.Final.omegaInacc_κ₁
#print axioms Erdos1220.Final.cofinal_κ₁
#print axioms Erdos1220.Final.hyp₁_of_HCof
