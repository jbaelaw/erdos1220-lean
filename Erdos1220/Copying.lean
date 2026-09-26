import Erdos1220.Amalgamation

/-!
# Copying an increasing family below a terminal condition

Each earlier condition is transported through the terminal tame isomorphism.
The transported condition remains a subcondition of the target and transport
preserves the extension relation. These are the algebraic ingredients for
copying a history, rather than merely its last graph.
-/

open Cardinal Set

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}

def restrict (p : BasicCondition V I block μ) (s : Set V) (hs : s ⊆ p.support) :
    BasicCondition V I block μ where
  support := s
  blue x y := p.blue x y ∧ x ∈ s ∧ y ∈ s
  symmetric := fun h => ⟨p.symmetric h.1, h.2.2, h.2.1⟩
  irreflexive := fun x h => p.irreflexive x h.1
  blue_support := fun h => h.2
  different_blocks := fun h => p.different_blocks h.1
  small := (Cardinal.mk_le_mk_of_subset hs).trans p.small

theorem restrict_extends (p : BasicCondition V I block μ) (s : Set V)
    (hs : s ⊆ p.support) : Extends (restrict p s hs) p := by
  refine ⟨hs, ?_⟩
  intro x hx y hy
  exact ⟨fun h => ⟨h, hx, hy⟩, And.left⟩

theorem restrict_mono (p : BasicCondition V I block μ) (s t : Set V)
    (hs : s ⊆ p.support) (ht : t ⊆ p.support) (hst : s ⊆ t) :
    Extends (restrict p s hs) (restrict p t ht) := by
  refine ⟨hst, ?_⟩
  intro x hx y hy
  exact ⟨fun h => ⟨h.1, hx, hy⟩, fun h => ⟨h.1, hst hx, hst hy⟩⟩

variable {p q : BasicCondition V I block μ}

def TameIso.copyPoint (iso : TameIso p q) (r : BasicCondition V I block μ)
    (hr : Extends r p) (x : r.support) : V :=
  iso.toEquiv ⟨x, hr.1 x.property⟩

theorem TameIso.copyPoint_injective (iso : TameIso p q)
    (r : BasicCondition V I block μ) (hr : Extends r p) :
    Function.Injective (iso.copyPoint r hr) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : p.support => (z : V))
    (iso.toEquiv.injective (Subtype.ext h))

theorem TameIso.copyPoint_range_subset (iso : TameIso p q)
    (r : BasicCondition V I block μ) (hr : Extends r p) :
    Set.range (iso.copyPoint r hr) ⊆ q.support := by
  rintro z ⟨x, rfl⟩
  exact (iso.toEquiv ⟨x, hr.1 x.property⟩).property

def TameIso.copy (iso : TameIso p q) (r : BasicCondition V I block μ)
    (hr : Extends r p) : BasicCondition V I block μ :=
  restrict q (Set.range (iso.copyPoint r hr)) (iso.copyPoint_range_subset r hr)

theorem TameIso.copy_extends (iso : TameIso p q)
    (r : BasicCondition V I block μ) (hr : Extends r p) :
    Extends (iso.copy r hr) q :=
  restrict_extends q _ _

theorem TameIso.copy_blue_iff (iso : TameIso p q)
    (r : BasicCondition V I block μ) (hr : Extends r p) (x y : r.support) :
    (iso.copy r hr).blue (iso.copyPoint r hr x) (iso.copyPoint r hr y) ↔ r.blue x y := by
  constructor
  · intro h
    have hp : p.blue x y := (iso.blue_iff _ _).mp h.1
    exact (hr.2 x x.property y y.property).mp hp
  · intro h
    refine ⟨?_, ⟨x, rfl⟩, ⟨y, rfl⟩⟩
    exact (iso.blue_iff _ _).mpr ((hr.2 x x.property y y.property).mpr h)

/-- A genuine isomorphism of the entire earlier partial coloring. -/
noncomputable def TameIso.copyIso (iso : TameIso p q)
    (r : BasicCondition V I block μ) (hr : Extends r p) : TameIso r (iso.copy r hr) where
  toEquiv := Equiv.ofInjective (iso.copyPoint r hr) (iso.copyPoint_injective r hr)
  blue_iff x y := iso.copy_blue_iff r hr x y
  block_iff x y := iso.block_iff ⟨x, hr.1 x.property⟩ ⟨y, hr.1 y.property⟩

/-- Every comparison in the source history survives the copy. -/
theorem TameIso.copy_mono (iso : TameIso p q)
    (r s : BasicCondition V I block μ) (hr : Extends r p) (hs : Extends s p)
    (hrs : Extends r s) : Extends (iso.copy r hr) (iso.copy s hs) := by
  apply restrict_mono
  rintro z ⟨x, rfl⟩
  exact ⟨⟨x, hrs.1 x.property⟩, rfl⟩

end Erdos1220.BasicCondition

#print axioms Erdos1220.BasicCondition.TameIso.copy_blue_iff
#print axioms Erdos1220.BasicCondition.TameIso.copy_mono
