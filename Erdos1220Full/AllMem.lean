import Erdos1220Full.BlueExclusion

/-!
# One condition containing `μ` prescribed vertices

A corollary of `HistoryForcing.exists_forall_dense` (strategic closure inside
the covering preorder): below any condition there is a single condition whose
terminal support contains any prescribed family of at most `μ` vertices.
-/

open Cardinal Set Order

universe u w

namespace Erdos1220Full

namespace HistoryForcing

open Erdos1220 Erdos1220.BasicCondition Erdos1220.BPHistory

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

theorem CHP0.exists_le_all_mem [Nonempty (CHP0 V I block μ hμ)] (q : CHP0 V I block μ hμ)
    {J : Type w} (v : J → V) (hJ : Cardinal.lift.{u} #J ≤ Cardinal.lift.{w} μ) :
    ∃ r, r ≤ q ∧ ∀ j, v j ∈ r.last.support := by
  classical
  have hJ' : Cardinal.lift.{u} #J ≤ Cardinal.lift.{w} #(μ.ord.ToType) := by
    rwa [Cardinal.mk_toType, Cardinal.card_ord]
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hJ'
  let J' : Type u := Set.range f
  have hJ'μ : #J' ≤ μ := by
    refine (Cardinal.mk_le_mk_of_subset (Set.subset_univ _)).trans ?_
    rw [Cardinal.mk_univ, Cardinal.mk_toType, Cardinal.card_ord]
  let D : J' → CHP0 V I block μ hμ → Prop := fun j' r => ∀ j, f j = j'.1 → v j ∈ r.last.support
  have hmono : ∀ j' r s, s ≤ r → D j' r → D j' s :=
    fun j' r s hsr h j hj => (CHP0.last_extends hsr).1 (h j hj)
  have hdense : ∀ j' p, p ≤ q → ∃ r, r ≤ p ∧ D j' r := by
    rintro ⟨_, ⟨j₀, rfl⟩⟩ p _
    obtain ⟨r, hr, hmem⟩ := p.exists_le_mem (v j₀)
    refine ⟨r, hr, fun j hj => ?_⟩
    rw [f.injective hj]
    exact hmem
  obtain ⟨r, hr, hD⟩ := exists_forall_dense hJ'μ q D hmono hdense
  exact ⟨r, hr, fun j => hD ⟨f j, j, rfl⟩ j rfl⟩

end HistoryForcing

end Erdos1220Full

#print axioms Erdos1220Full.HistoryForcing.CHP0.exists_le_all_mem
