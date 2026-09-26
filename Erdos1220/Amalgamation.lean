import Erdos1220.BasicConditions

/-!
# Amalgamation of partial colorings

The all-red and one-blue-cross-edge constructions in Shelah–Stanley §3.3.
All support, size, symmetry, and old-color preservation properties are proved.
Tame isomorphisms retain the block-equivalence relation. Their overlap-fixing
property implies the compatibility needed by the concrete constructions.
-/

open Cardinal Set

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}

/-- The two colorings agree on their common domain. -/
def AgreeOnOverlap (p q : BasicCondition V I block μ) : Prop :=
  ∀ x ∈ p.support ∩ q.support, ∀ y ∈ p.support ∩ q.support,
    p.blue x y ↔ q.blue x y

theorem AgreeOnOverlap.symm {p q : BasicCondition V I block μ}
    (h : AgreeOnOverlap p q) : AgreeOnOverlap q p := by
  intro x hx y hy
  exact (h x ⟨hx.2, hx.1⟩ y ⟨hy.2, hy.1⟩).symm

/-- A block-class preserving graph isomorphism of the supported colorings. -/
structure TameIso (p q : BasicCondition V I block μ) where
  toEquiv : p.support ≃ q.support
  blue_iff : ∀ x y : p.support,
    q.blue (toEquiv x) (toEquiv y) ↔ p.blue x y
  block_iff : ∀ x y : p.support,
    block (toEquiv x) = block (toEquiv y) ↔ block x = block y

def TameIso.FixesOverlap {p q : BasicCondition V I block μ} (e : TameIso p q) : Prop :=
  ∀ x : p.support, (x : V) ∈ q.support → (e.toEquiv x : V) = x

/-- The induced block map fixes blocks occurring on both sides. -/
def TameIso.FixesSharedBlocks {p q : BasicCondition V I block μ}
    (e : TameIso p q) : Prop :=
  ∀ x : p.support, block x ∈ block '' q.support → block (e.toEquiv x) = block x

theorem TameIso.agreeOnOverlap {p q : BasicCondition V I block μ}
    (e : TameIso p q) (he : e.FixesOverlap) : AgreeOnOverlap p q := by
  intro x hx y hy
  have h := e.blue_iff ⟨x, hx.1⟩ ⟨y, hy.1⟩
  rw [he ⟨x, hx.1⟩ hx.2, he ⟨y, hy.1⟩ hy.2] at h
  exact h.symm

theorem union_small (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ) :
    #(p.support ∪ q.support : Set V) ≤ μ := by
  calc
    #(p.support ∪ q.support : Set V) ≤ #p.support + #q.support := Cardinal.mk_union_le _ _
    _ ≤ μ + μ := add_le_add p.small q.small
    _ = μ := Cardinal.add_eq_self hμ

/-- New cross edges are all red. -/
def redAmalgam (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ) :
    BasicCondition V I block μ where
  support := p.support ∪ q.support
  blue x y := p.blue x y ∨ q.blue x y
  symmetric := fun h => h.elim (fun h => Or.inl (p.symmetric h))
    (fun h => Or.inr (q.symmetric h))
  irreflexive := fun x h => h.elim (p.irreflexive x) (q.irreflexive x)
  blue_support := by
    intro x y h
    rcases h with h | h
    · exact ⟨Or.inl (p.blue_support h).1, Or.inl (p.blue_support h).2⟩
    · exact ⟨Or.inr (q.blue_support h).1, Or.inr (q.blue_support h).2⟩
  different_blocks := fun h => h.elim p.different_blocks q.different_blocks
  small := union_small p q hμ

theorem extends_redAmalgam_left (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (h : AgreeOnOverlap p q) : Extends p (redAmalgam p q hμ) := by
  refine ⟨subset_union_left, ?_⟩
  intro x hx y hy
  constructor
  · intro hb
    rcases hb with hp | hq
    · exact hp
    · exact (h x ⟨hx, (q.blue_support hq).1⟩ y ⟨hy, (q.blue_support hq).2⟩).mpr hq
  · exact Or.inl

theorem extends_redAmalgam_right (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (h : AgreeOnOverlap p q) : Extends q (redAmalgam p q hμ) := by
  refine ⟨subset_union_right, ?_⟩
  intro x hx y hy
  constructor
  · intro hb
    rcases hb with hp | hq
    · exact (h x ⟨(p.blue_support hp).1, hx⟩ y ⟨(p.blue_support hp).2, hy⟩).mp hp
    · exact hq
  · exact Or.inr

/-- A permissible single new blue edge, crossing the two non-overlap parts. -/
structure CrossEdge (p q : BasicCondition V I block μ) where
  left : V
  right : V
  left_mem : left ∈ p.support
  left_not_mem : left ∉ q.support
  right_mem : right ∈ q.support
  right_not_mem : right ∉ p.support
  block_ne : block left ≠ block right

namespace CrossEdge

variable {p q : BasicCondition V I block μ}

def Adj (e : CrossEdge p q) (x y : V) : Prop :=
  (x = e.left ∧ y = e.right) ∨ (x = e.right ∧ y = e.left)

theorem adj_symm (e : CrossEdge p q) {x y : V} (h : e.Adj x y) : e.Adj y x :=
  h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)

theorem not_adj_left (e : CrossEdge p q) {x y : V}
    (hx : x ∈ p.support) (hy : y ∈ p.support) : ¬ e.Adj x y := by
  rintro (⟨_, rfl⟩ | ⟨rfl, _⟩)
  · exact e.right_not_mem hy
  · exact e.right_not_mem hx

theorem not_adj_right (e : CrossEdge p q) {x y : V}
    (hx : x ∈ q.support) (hy : y ∈ q.support) : ¬ e.Adj x y := by
  rintro (⟨rfl, _⟩ | ⟨_, rfl⟩)
  · exact e.left_not_mem hx
  · exact e.left_not_mem hy

theorem adj_blocks_ne (e : CrossEdge p q) {x y : V} (h : e.Adj x y) :
    block x ≠ block y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact e.block_ne
  · exact e.block_ne.symm

theorem adj_support (e : CrossEdge p q) {x y : V} (h : e.Adj x y) :
    x ∈ p.support ∪ q.support ∧ y ∈ p.support ∪ q.support := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Or.inl e.left_mem, Or.inr e.right_mem⟩
  · exact ⟨Or.inr e.right_mem, Or.inl e.left_mem⟩

end CrossEdge

/-- The chosen fresh edge is blue; every other new cross edge is red. -/
def blueAmalgam (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (e : CrossEdge p q) : BasicCondition V I block μ where
  support := p.support ∪ q.support
  blue x y := (redAmalgam p q hμ).blue x y ∨ e.Adj x y
  symmetric := fun h => h.elim
    (fun h => Or.inl ((redAmalgam p q hμ).symmetric h))
    (fun h => Or.inr (e.adj_symm h))
  irreflexive := by
    intro x h
    rcases h with h | h
    · exact (redAmalgam p q hμ).irreflexive x h
    · exact e.adj_blocks_ne h rfl
  blue_support := fun h => h.elim (redAmalgam p q hμ).blue_support e.adj_support
  different_blocks := fun h => h.elim
    (redAmalgam p q hμ).different_blocks e.adj_blocks_ne
  small := union_small p q hμ

theorem extends_blueAmalgam_left (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (h : AgreeOnOverlap p q) (e : CrossEdge p q) : Extends p (blueAmalgam p q hμ e) := by
  refine ⟨subset_union_left, ?_⟩
  intro x hx y hy
  constructor
  · intro hb
    exact ((extends_redAmalgam_left p q hμ h).2 x hx y hy).mp
      (hb.resolve_right (e.not_adj_left hx hy))
  · intro hb
    exact Or.inl (((extends_redAmalgam_left p q hμ h).2 x hx y hy).mpr hb)

theorem extends_blueAmalgam_right (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (h : AgreeOnOverlap p q) (e : CrossEdge p q) : Extends q (blueAmalgam p q hμ e) := by
  refine ⟨subset_union_right, ?_⟩
  intro x hx y hy
  constructor
  · intro hb
    exact ((extends_redAmalgam_right p q hμ h).2 x hx y hy).mp
      (hb.resolve_right (e.not_adj_right hx hy))
  · intro hb
    exact Or.inl (((extends_redAmalgam_right p q hμ h).2 x hx y hy).mpr hb)

theorem blueAmalgam_has_chosen_edge (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (e : CrossEdge p q) : (blueAmalgam p q hμ e).blue e.left e.right :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem blueAmalgam_cross_iff (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (e : CrossEdge p q) {x y : V} (hxq : x ∉ q.support) (hyp : y ∉ p.support) :
    (blueAmalgam p q hμ e).blue x y ↔ e.Adj x y := by
  constructor
  · rintro ((hp | hq) | hnew)
    · exact False.elim (hyp (p.blue_support hp).2)
    · exact False.elim (hxq (q.blue_support hq).1)
    · exact hnew
  · exact Or.inr

/-- The concrete one-blue-edge amalgamation theorem needed at successor stages. -/
theorem exists_blue_amalgamation (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (iso : TameIso p q) (hiso : iso.FixesOverlap) (e : CrossEdge p q) :
    ∃ r : BasicCondition V I block μ,
      Extends p r ∧ Extends q r ∧ r.blue e.left e.right := by
  have h := iso.agreeOnOverlap hiso
  exact ⟨blueAmalgam p q hμ e, extends_blueAmalgam_left p q hμ h e,
    extends_blueAmalgam_right p q hμ h e, blueAmalgam_has_chosen_edge p q hμ e⟩

end Erdos1220.BasicCondition

#print axioms Erdos1220.BasicCondition.exists_blue_amalgamation
#print axioms Erdos1220.BasicCondition.blueAmalgam_cross_iff
