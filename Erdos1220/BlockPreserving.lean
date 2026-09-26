import Erdos1220.EdgeOrigin

/-!
# Histories whose copies preserve block labels

This is a restriction of the earlier candidate history construction. Merely
requiring immediate source separation does not separate the entire ancestral
paths of blue-adjacent vertices. Global preservation of block labels does.
The existence/density/chain-condition obligations for this restricted forcing
are separate from the invariant proved here.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}
variable {p q : BasicCondition V I block μ}

def TameIso.PreservesBlocks (iso : TameIso p q) : Prop :=
  ∀ x : p.support, block (iso.toEquiv x) = block x

theorem TameIso.PreservesBlocks.symm_apply {iso : TameIso p q}
    (h : iso.PreservesBlocks) (y : q.support) :
    block (iso.toEquiv.symm y) = block y := by
  simpa only [Equiv.apply_symm_apply] using (h (iso.toEquiv.symm y)).symm

theorem TameIso.PreservesBlocks.fixesSharedBlocks {iso : TameIso p q}
    (h : iso.PreservesBlocks) : iso.FixesSharedBlocks :=
  fun x _ => h x

theorem CrossEdge.sourceSeparated_of_preservesBlocks (e : CrossEdge p q)
    (iso : TameIso p q) (h : iso.PreservesBlocks) : e.SourceSeparated iso := by
  unfold CrossEdge.SourceSeparated
  rw [h.symm_apply]
  exact e.block_ne

end Erdos1220.BasicCondition

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

def BlockPreserving (H : History V I block μ hμ) : Prop :=
  ∀ i (hi : Order.succ i ≤ H.length), (H.step i hi).iso.PreservesBlocks

theorem BlockPreserving.truncate {H : History V I block μ hμ}
    (hH : H.BlockPreserving) (δ : Ordinal.{u}) (hδ : δ ≤ H.length) :
    (H.truncate δ hδ).BlockPreserving :=
  fun i hi => hH i (hi.trans hδ)

theorem ParentWitness.block_eq {H : History V I block μ hμ}
    (hH : H.BlockPreserving) {x : H.last.support} (w : ParentWitness H x) :
    block w.point = block x := by
  rw [w.point_eq]
  have h := hH w.index w.next_le
    ((H.step w.index w.next_le).parent ⟨x, w.at_next⟩ w.is_new)
  rw [(H.step w.index w.next_le).parent_maps_to] at h
  exact h.symm

/-- Every point on the finite ancestry path has the descendant's block label. -/
theorem BlockPreserving.ancestry_block {H : History V I block μ hμ}
    (hH : H.BlockPreserving) (x : H.last.support) (z : Ordinal.{u} × V)
    (hz : z ∈ H.ancestry x) : block z.2 = block x := by
  classical
  rw [ancestry] at hz
  split at hz
  · have heq := List.mem_singleton.mp hz
    cases heq
    rfl
  · rcases List.mem_cons.mp hz with rfl | hz
    · rfl
    · exact (hH.ancestry_block _ z hz).trans (ParentWitness.block_eq hH _)
termination_by H.birth x
decreasing_by
  exact (H.parentWitness x _).birth_lt

/-- Ancestors of blue-adjacent vertices cannot even occupy the same block. -/
theorem BlockPreserving.ancestry_blocks_ne {H : History V I block μ hμ}
    (hH : H.BlockPreserving) (x y : H.last.support) (hb : H.last.blue x y)
    (z w : Ordinal.{u} × V) (hz : z ∈ H.ancestry x) (hw : w ∈ H.ancestry y) :
    block z.2 ≠ block w.2 := by
  rw [hH.ancestry_block x z hz, hH.ancestry_block y w hw]
  exact H.last.different_blocks hb

end Erdos1220.History

#print axioms Erdos1220.History.BlockPreserving.ancestry_blocks_ne
