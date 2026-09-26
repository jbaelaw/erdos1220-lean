/-
Parts of the fiber-antichain proof are adapted from Flypitch4/Forcing.lean.
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0; see LICENSE and NOTICE.
Original authors: Jesse Han, Floris van Doorn. Lean 4 port: Ian Klatzco, Claude.
-/

import Flypitch4.Forcing

/-!
# Higher chain conditions and preservation of large cardinal comparisons

Flypitch supplies a CCC version. Here the same Boolean-valued argument is
proved for an arbitrary cardinal bound `κ`, as required by the higher chain
condition in the Shelah–Stanley forcing.

The target Boolean algebra must still be constructed and shown to satisfy
`ChainCondition κ`. This module does not assume or conclude that the as-yet
unconstructed 1220 forcing has that property.
-/

open Cardinal Set Flypitch bSet

universe u

namespace Erdos1220Full

/-- Every indexed family of pairwise disjoint positive elements has size `< κ`. -/
def ChainCondition (κ : Cardinal.{u}) (𝔹 : Type u)
    [NontrivialCompleteBooleanAlgebra 𝔹] : Prop :=
  ∀ (ι : Type u) (a : ι → 𝔹),
    (∀ i, ⊥ < a i) →
    (∀ i j, i ≠ j → a i ⊓ a j ≤ ⊥) → #ι < κ

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
variable {κ : Cardinal.{u}}

/-- A putative functional name produces an antichain on each fiber of the
external choice of preimages. Hence that fiber has size below the chain bound. -/
theorem fiber_lt_of_chainCondition (hcc : ChainCondition κ 𝔹)
    (x y : PSet.{u})
    (hy : ∀ i j, i ≠ j → ¬ PSet.Equiv (y.Func i) (y.Func j))
    (f : bSet 𝔹) (g : y.Type → x.Type)
    (hg : ∀ i : y.Type,
      (⊥ : 𝔹) < is_func f ⊓ pair (check (x.Func (g i))) (check (y.Func i)) ∈ᴮ f)
    (ξ : x.Type) : #(g ⁻¹' {ξ}) < κ := by
  let a : (g ⁻¹' {ξ}) → 𝔹 := fun i =>
    is_func f ⊓ pair (check (x.Func (g i.val))) (check (y.Func i.val)) ∈ᴮ f
  apply hcc (g ⁻¹' {ξ}) a (fun i => hg i.val)
  intro i j hij
  apply poset_yoneda
  intro Γ hΓ
  obtain ⟨hi, hj⟩ := le_inf_iff.mp hΓ
  obtain ⟨hfunc, hmemi⟩ := le_inf_iff.mp hi
  obtain ⟨_, hmemj⟩ := le_inf_iff.mp hj
  have hgi : g i.val = ξ := i.property
  have hgj : g j.val = ξ := j.property
  rw [hgi] at hmemi
  rw [hgj] at hmemj
  have heq : Γ ≤ check (y.Func i.val) =ᴮ check (y.Func j.val) :=
    eq_of_is_func_of_eq hfunc bv_refl hmemi hmemj
  apply heq.trans
  rw [le_bot_iff]
  exact check_bv_eq_bot_of_not_equiv (hy _ _ (fun h => hij (Subtype.ext h)))

/-- Under the chain condition, an infinite represented domain of cardinality
at least `κ` cannot acquire a surjection onto a larger injectively represented set.
The conclusion is a Boolean value equal to bottom, not a bare external claim. -/
theorem surjects_onto_eq_bot_of_chainCondition (hcc : ChainCondition κ 𝔹)
    (x y : PSet.{u}) (hx : ℵ₀ ≤ #x.Type) (hκ : κ ≤ #x.Type)
    (hxy : #x.Type < #y.Type)
    (hy : ∀ i j, i ≠ j → ¬ PSet.Equiv (y.Func i) (y.Func j))
    (hy_nonempty : ∃ z, z ∈ y) :
    (surjects_onto (check x) (check y) : 𝔹) = ⊥ := by
  classical
  apply le_bot_iff.mp
  apply poset_yoneda
  intro Γ hΓ
  by_cases hzero : Γ = ⊥
  · exact hzero.le
  have hpos : ⊥ < Γ := bot_lt_iff_ne_bot.mpr hzero
  obtain ⟨f, hf⟩ := AE_of_check_larger_than_check' hpos hΓ hy_nonempty
  choose g hg using hf
  obtain ⟨ξ, hξ⟩ := Cardinal.infinite_pigeonhole_card_lt g hxy (hx.trans hxy.le)
  have hsmall := fiber_lt_of_chainCondition hcc x y hy f g hg ξ
  exact False.elim ((hκ.trans hξ.le).not_gt hsmall)

end Erdos1220Full

#print axioms Erdos1220Full.fiber_lt_of_chainCondition
#print axioms Erdos1220Full.surjects_onto_eq_bot_of_chainCondition
