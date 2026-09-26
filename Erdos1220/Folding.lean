import Erdos1220.Amalgamation

/-!
# Folding a copied partial coloring back to its source

The overlap-fixing isomorphism makes the two descriptions of a root vertex
agree. Every inherited blue edge folds to a blue edge of the source. A newly
introduced blue edge is the one exception; its source-block condition is kept
explicit below rather than silently assumed.

The final source-block hypothesis is an additional admissibility condition for
a candidate history construction. This file does NOT prove that every weak
amalgamation from `Amalgamation.lean` satisfies it.
-/

open Cardinal Set

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}
variable {p q : BasicCondition V I block μ}

/-- Old vertices stay fixed; new copied vertices return to their preimages. -/
noncomputable def TameIso.fold (iso : TameIso p q)
    (x : (p.support ∪ q.support : Set V)) : p.support := by
  classical
  exact if hx : (x : V) ∈ p.support then ⟨x, hx⟩
    else iso.toEquiv.symm ⟨x, x.property.resolve_left hx⟩

theorem TameIso.fold_of_left (iso : TameIso p q)
    (x : (p.support ∪ q.support : Set V)) (hx : (x : V) ∈ p.support) :
    iso.fold x = ⟨x, hx⟩ := by
  classical
  simp only [TameIso.fold, dite_eq_left hx]

theorem TameIso.fold_of_right (iso : TameIso p q) (hiso : iso.FixesOverlap)
    (x : (p.support ∪ q.support : Set V)) (hx : (x : V) ∈ q.support) :
    iso.fold x = iso.toEquiv.symm ⟨x, hx⟩ := by
  classical
  by_cases hxp : (x : V) ∈ p.support
  · rw [iso.fold_of_left x hxp]
    apply iso.toEquiv.injective
    apply Subtype.ext
    simpa only [Equiv.apply_symm_apply] using hiso ⟨x, hxp⟩ hx
  · simp only [TameIso.fold, dite_eq_right hxp]

theorem TameIso.fold_inherited_blue (iso : TameIso p q) (hiso : iso.FixesOverlap)
    (hμ : ℵ₀ ≤ μ) (x y : (p.support ∪ q.support : Set V))
    (hblue : (redAmalgam p q hμ).blue x y) : p.blue (iso.fold x) (iso.fold y) := by
  rcases hblue with hp | hq
  · obtain ⟨hx, hy⟩ := p.blue_support hp
    rw [iso.fold_of_left x hx, iso.fold_of_left y hy]
    exact hp
  · obtain ⟨hx, hy⟩ := q.blue_support hq
    rw [iso.fold_of_right hiso x hx, iso.fold_of_right hiso y hy]
    apply (iso.blue_iff _ _).mp
    simpa only [Equiv.apply_symm_apply] using hq

/-- A new edge must connect distinct source blocks if it is to preserve
source-block separation under folding. -/
def CrossEdge.SourceSeparated (e : CrossEdge p q) (iso : TameIso p q) : Prop :=
  block e.left ≠ block (iso.toEquiv.symm ⟨e.right, e.right_mem⟩)

theorem TameIso.preimage_block_eq_of_shared (iso : TameIso p q)
    (hiso : iso.FixesSharedBlocks) (y : q.support)
    (hy : block y ∈ block '' p.support) :
    block (iso.toEquiv.symm y) = block y := by
  obtain ⟨x, hx, hxy⟩ := hy
  have hxq : block x ∈ block '' q.support := ⟨y, y.property, hxy.symm⟩
  have himage : block (iso.toEquiv ⟨x, hx⟩) =
      block (iso.toEquiv (iso.toEquiv.symm y)) := by
    simpa only [Equiv.apply_symm_apply] using (hiso ⟨x, hx⟩ hxq).trans hxy
  exact ((iso.block_iff ⟨x, hx⟩ (iso.toEquiv.symm y)).mp himage).symm.trans hxy

/-- In a shared target block, source separation follows from the original
tame-map conditions and the requirement that the selected edge crosses blocks. -/
theorem CrossEdge.sourceSeparated_of_shared_block (e : CrossEdge p q)
    (iso : TameIso p q) (hiso : iso.FixesSharedBlocks)
    (hshared : block e.right ∈ block '' p.support) : e.SourceSeparated iso := by
  unfold CrossEdge.SourceSeparated
  rw [iso.preimage_block_eq_of_shared hiso ⟨e.right, e.right_mem⟩ hshared]
  exact e.block_ne

theorem TameIso.fold_blue_blocks_ne (iso : TameIso p q) (hiso : iso.FixesOverlap)
    (hμ : ℵ₀ ≤ μ) (e : CrossEdge p q) (he : e.SourceSeparated iso)
    (x y : (p.support ∪ q.support : Set V))
    (hblue : (blueAmalgam p q hμ e).blue x y) :
    block (iso.fold x) ≠ block (iso.fold y) := by
  rcases hblue with hold | hnew
  · exact p.different_blocks (iso.fold_inherited_blue hiso hμ x y hold)
  · rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    rcases hnew with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [iso.fold_of_left _ e.left_mem, iso.fold_of_right hiso _ e.right_mem]
      exact he
    · rw [iso.fold_of_right hiso _ e.right_mem, iso.fold_of_left _ e.left_mem]
      exact he.symm

/-- The vertex-overlap fixing implies that shared source/target blocks can
use the original different-block condition to discharge source separation. -/
theorem CrossEdge.sourceSeparated_of_fixed_right_block (e : CrossEdge p q)
    (iso : TameIso p q)
    (hblock : block (iso.toEquiv.symm ⟨e.right, e.right_mem⟩) = block e.right) :
    e.SourceSeparated iso := by
  unfold CrossEdge.SourceSeparated
  rw [hblock]
  exact e.block_ne

end Erdos1220.BasicCondition

#print axioms Erdos1220.BasicCondition.TameIso.fold_inherited_blue
#print axioms Erdos1220.BasicCondition.TameIso.fold_blue_blocks_ne
