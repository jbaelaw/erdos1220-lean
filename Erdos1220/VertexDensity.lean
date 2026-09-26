import Erdos1220.Relabel
import Erdos1220.BlockPreservingClosure

/-!
# Adding an arbitrary vertex by a pure extension

If every block already has a supported point, a missing vertex can be
inserted by exchanging it with a supported point of the same block and
taking the red amalgam with the resulting copy. The exchange fixes the
overlap. The recorded successor therefore preserves the entire old
history and the actual block labels.
-/

open Cardinal Set Order

universe u v

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}

/-- A swap inside a represented block supplies an actual admissible red
transition containing a previously unsupported vertex. -/
theorem exists_vertex_transition (p : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (a z : V) (ha : a ∈ p.support) (hz : z ∉ p.support)
    (haz : block a = block z) :
    ∃ r : BasicCondition V I block μ, ∃ t : Transition hμ p r,
      t.iso.PreservesBlocks ∧ z ∈ r.support := by
  classical
  let e : V ≃ V := Equiv.swap a z
  have hea : e a = z := Equiv.swap_apply_left a z
  have hez : e z = a := Equiv.swap_apply_right a z
  have he : ∀ x, block (e x) = block x := by
    intro x
    by_cases hxa : x = a
    · subst x
      rw [hea]
      exact haz.symm
    by_cases hxz : x = z
    · subst x
      rw [hez]
      exact haz
    change block (Equiv.swap a z x) = block x
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxz]
  let q := p.relabel e he
  let iso := p.relabelIso e he
  have hpres : iso.PreservesBlocks := p.relabelIso_preservesBlocks e he
  have hfix : iso.FixesOverlap := by
    intro x hx
    change e.symm (x : V) ∈ p.support at hx
    have hxa : (x : V) ≠ a := by
      intro h
      have hes : e.symm a = z :=
        e.injective ((e.apply_symm_apply a).trans hez.symm)
      apply hz
      simpa only [h, hes] using hx
    have hxz : (x : V) ≠ z := fun h => hz (h ▸ x.property)
    change Equiv.swap a z (x : V) = x
    exact Equiv.swap_apply_of_ne_of_ne hxa hxz
  let r := redAmalgam p q hμ
  let t : Transition hμ p r := {
    right := q
    iso := iso
    fixesOverlap := hfix
    fixesSharedBlocks := hpres.fixesSharedBlocks
    edge := none
    sourceSeparated := by intro edge h; cases h
    result_eq := rfl }
  refine ⟨r, t, hpres, ?_⟩
  change z ∈ p.support ∪ q.support
  apply Or.inr
  simpa only [hea] using (p.relabel_mem e he a).mpr ha

end Erdos1220.BasicCondition

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

private theorem transported_heq {α β : Sort v} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  exact HEq.rfl

/-- Successor append preserves all old states and all old recorded data. -/
theorem pureExtends_append (H : History V I block μ hμ)
    (r : BasicCondition V I block μ) (t : Transition hμ H.last r) :
    PureExtends H (H.append r t) := by
  refine ⟨Order.le_succ H.length, ?_, ?_⟩
  · intro i hi
    exact (H.append_preserves_state r t i hi).symm
  · intro i hi
    have hne : i ≠ H.length := ((Order.lt_succ i).trans_le hi).ne
    have hs : HEq ((H.append r t).step i (hi.trans (Order.le_succ H.length)))
        (H.step i hi) := by
      simp only [History.append, dite_eq_right hne, transported_heq]
    exact hs.symm

/-- Vertex membership is dense among block-preserving histories meeting
every block, with the density witnessed by a pure extension. -/
theorem exists_pure_extension_mem (H : History V I block μ hμ)
    (hH : H.BlockPreserving)
    (hcover : ∀ i : I, ∃ x ∈ H.last.support, block x = i) (z : V) :
    ∃ K : History V I block μ hμ, PureExtends H K ∧ K.BlockPreserving ∧
      z ∈ K.last.support ∧ (∀ i : I, ∃ x ∈ K.last.support, block x = i) := by
  classical
  by_cases hz : z ∈ H.last.support
  · exact ⟨H, pureExtends_refl H, hH, hz, hcover⟩
  obtain ⟨a, ha, haz⟩ := hcover (block z)
  obtain ⟨r, t, ht, hzr⟩ := H.last.exists_vertex_transition hμ a z ha hz haz
  have hpure : PureExtends H (H.append r t) := H.pureExtends_append r t
  refine ⟨H.append r t, hpure, hH.append r t ht, ?_, ?_⟩
  · simpa only [H.append_last r t] using hzr
  · intro i
    obtain ⟨x, hx, hxi⟩ := hcover i
    exact ⟨x, hpure.last_extends.1 hx, hxi⟩

end Erdos1220.History

#print axioms Erdos1220.BasicCondition.exists_vertex_transition
#print axioms Erdos1220.History.pureExtends_append
#print axioms Erdos1220.History.exists_pure_extension_mem
