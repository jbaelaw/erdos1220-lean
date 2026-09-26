import Erdos1220.BlueOrigin
import Erdos1220.AncestralEvents
import Erdos1220.FiniteCover

/-!
# Blue cliques in block-preserving histories are countable

Every blue pair has a selected ancestor edge. Its creation stage belongs to
one of the finite ancestry paths. That stage supplies only two block labels;
distinct vertices in a clique have distinct blocks. Thus every vertex forbids
only finitely many other clique vertices and the finite map covers all pairs.
An elementary countability lemma completes the proof.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.History

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

theorem BlockPreserving.blue_clique_countable {H : History V I block μ hμ}
    (hH : H.BlockPreserving) (C : Set V) (hC : C ⊆ H.last.support)
    (hblue : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → H.last.blue x y) : Countable C := by
  classical
  let vertex : C → H.last.support := fun x => ⟨x, hC x.property⟩
  let label : C → I := fun x => block x
  have hinj : Function.Injective label := by
    intro x y heq
    apply Subtype.ext
    by_contra hne
    exact H.last.different_blocks (hblue x x.property y y.property hne) heq
  let f : C → Set C := fun x => label ⁻¹' H.ancestralEventBlocks (vertex x)
  have hf : ∀ x, (f x).Finite := by
    intro x
    exact Set.Finite.preimage hinj.injOn (H.finite_ancestralEventBlocks (vertex x))
  apply Erdos1220.countable_of_finite_pair_cover f hf
  intro x y hxy
  have hne : (x : V) ≠ y := fun h => hxy (Subtype.ext h)
  have hb : H.last.blue (vertex x) (vertex y) := hblue x x.property y y.property hne
  obtain ⟨z, hz, w, hw, i, hi, he, hs⟩ := H.blue_has_ancestral_origin (vertex x) (vertex y) hb
  obtain ⟨hzblock, hwblock⟩ := (H.step i hi).newEdge_mem_eventBlocks he
  rcases hs with hs | hs
  · left
    change block (y : V) ∈ H.ancestralEventBlocks (vertex x)
    have hby : block w.2 = block (y : V) := hH.ancestry_block (vertex y) w hw
    rw [← hby]
    exact H.mem_ancestralEventBlocks (vertex x) z hz i hi hs hwblock
  · right
    change block (x : V) ∈ H.ancestralEventBlocks (vertex y)
    have hbx : block z.2 = block (x : V) := hH.ancestry_block (vertex x) z hz
    rw [← hbx]
    exact H.mem_ancestralEventBlocks (vertex y) w hw i hi hs hzblock

theorem BlockPreserving.blue_clique_cardinal_le_aleph0 {H : History V I block μ hμ}
    (hH : H.BlockPreserving) (C : Set V) (hC : C ⊆ H.last.support)
    (hblue : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → H.last.blue x y) : #C ≤ ℵ₀ := by
  let := hH.blue_clique_countable C hC hblue
  exact Cardinal.mk_le_aleph0

end Erdos1220.History

#print axioms Erdos1220.History.BlockPreserving.blue_clique_countable
#print axioms Erdos1220.History.BlockPreserving.blue_clique_cardinal_le_aleph0
