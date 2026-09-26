import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Basic conditions for the Shelah–Stanley construction

This implements the elementary poset of section 3.1 and its chain-union
closure from section 3.2. Blue records the non-red edges; edges outside the
support are absent. No clique-exclusion result is built into the definition.

This is the basic poset, NOT the history-enriched forcing of sections 3.4–3.9.
Its closure alone does not prove a negative partition relation.

Source: Shelah–Stanley, APAL 36 (1987), pp. 140–141.
-/

open Cardinal Set

universe u

namespace Erdos1220

/-- A partial coloring on at most `μ` vertices, red within each block. -/
structure BasicCondition (V I : Type u) (block : V → I) (μ : Cardinal.{u}) where
  support : Set V
  blue : V → V → Prop
  symmetric : ∀ {x y}, blue x y → blue y x
  irreflexive : ∀ x, ¬ blue x x
  blue_support : ∀ {x y}, blue x y → x ∈ support ∧ y ∈ support
  different_blocks : ∀ {x y}, blue x y → block x ≠ block y
  small : #support ≤ μ

namespace BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}

/-- `Extends p q` means that `q` is the stronger condition. -/
def Extends (p q : BasicCondition V I block μ) : Prop :=
  p.support ⊆ q.support ∧
    ∀ x ∈ p.support, ∀ y ∈ p.support, q.blue x y ↔ p.blue x y

theorem extends_refl (p : BasicCondition V I block μ) : Extends p p :=
  ⟨Subset.rfl, fun _ _ _ _ => Iff.rfl⟩

theorem Extends.trans {p q r : BasicCondition V I block μ}
    (hpq : Extends p q) (hqr : Extends q r) : Extends p r := by
  refine ⟨hpq.1.trans hqr.1, ?_⟩
  intro x hx y hy
  exact (hqr.2 x (hpq.1 hx) y (hpq.1 hy)).trans (hpq.2 x hx y hy)

section Union

variable {J : Type u} [Nonempty J]
    (p : J → BasicCondition V I block μ) (hJ : #J ≤ μ) (hμ : ℵ₀ ≤ μ)

include hJ hμ

theorem union_support_small : #(⋃ i, (p i).support) ≤ μ := by
  calc
    #(⋃ i, (p i).support) ≤ #J * ⨆ i, #(p i).support :=
      Cardinal.mk_iUnion_le _
    _ ≤ μ * μ := mul_le_mul' hJ (ciSup_le fun i => (p i).small)
    _ = μ := Cardinal.mul_eq_self hμ

/-- The union relation is a basic condition; being a chain is needed below
to ensure that no previously red edge becomes blue. -/
def chainUnion : BasicCondition V I block μ where
  support := ⋃ i, (p i).support
  blue x y := ∃ i, (p i).blue x y
  symmetric := by
    rintro x y ⟨i, h⟩
    exact ⟨i, (p i).symmetric h⟩
  irreflexive := by
    rintro x ⟨i, h⟩
    exact (p i).irreflexive x h
  blue_support := by
    rintro x y ⟨i, h⟩
    exact ⟨mem_iUnion.mpr ⟨i, ((p i).blue_support h).1⟩,
      mem_iUnion.mpr ⟨i, ((p i).blue_support h).2⟩⟩
  different_blocks := by
    rintro x y ⟨i, h⟩
    exact (p i).different_blocks h
  small := union_support_small p hJ hμ

variable [LinearOrder J]
    (hchain : ∀ i j, i ≤ j → Extends (p i) (p j))

include hchain

theorem extends_chainUnion (i : J) : Extends (p i) (chainUnion p hJ hμ) := by
  constructor
  · exact subset_iUnion (fun j => (p j).support) i
  · intro x hx y hy
    change (∃ j, (p j).blue x y) ↔ (p i).blue x y
    constructor
    · rintro ⟨j, hblue⟩
      rcases le_total i j with hij | hji
      · exact ((hchain i j hij).2 x hx y hy).mp hblue
      · obtain ⟨hxj, hyj⟩ := (p j).blue_support hblue
        exact ((hchain j i hji).2 x hxj y hyj).mpr hblue
    · exact fun hblue => ⟨i, hblue⟩

theorem chainUnion_least (q : BasicCondition V I block μ)
    (hq : ∀ i, Extends (p i) q) : Extends (chainUnion p hJ hμ) q := by
  constructor
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hq i).1 hi
  · intro x hx y hy
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    have hxk : x ∈ (p (max i j)).support :=
      (hchain i (max i j) (le_max_left _ _)).1 hxi
    have hyk : y ∈ (p (max i j)).support :=
      (hchain j (max i j) (le_max_right _ _)).1 hyj
    change q.blue x y ↔ ∃ k, (p k).blue x y
    constructor
    · intro hblue
      exact ⟨max i j, ((hq (max i j)).2 x hxk y hyk).mp hblue⟩
    · rintro ⟨k, hblue⟩
      obtain ⟨hxk, hyk⟩ := (p k).blue_support hblue
      exact ((hq k).2 x hxk y hyk).mpr hblue

/-- The actual union is a least upper bound for every nonempty increasing
chain with at most `μ` indices. -/
theorem exists_chain_lub :
    ∃ q : BasicCondition V I block μ,
      (∀ i, Extends (p i) q) ∧
      ∀ r, (∀ i, Extends (p i) r) → Extends q r := by
  exact ⟨chainUnion p hJ hμ, extends_chainUnion p hJ hμ hchain,
    chainUnion_least p hJ hμ hchain⟩

end Union
end BasicCondition
end Erdos1220

#print axioms Erdos1220.BasicCondition.exists_chain_lub
