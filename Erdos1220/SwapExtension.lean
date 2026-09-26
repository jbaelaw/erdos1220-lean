import Erdos1220.ConditionAlgebra

/-!
# Extending an overlap-fixing isomorphism by a canonical ambient swap

An overlap-fixing equivalence exchanges the two pure support differences.
Use the equivalence on its source, its inverse on the remaining target, and
the identity elsewhere. The result is an involution of the entire vertex
type. No size or spare-space hypothesis on the blocks is required.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}
variable {p q : BasicCondition V I block μ}

noncomputable def TameIso.swapMap (iso : TameIso p q) (x : V) : V := by
  classical
  exact if hx : x ∈ p.support then iso.toEquiv ⟨x, hx⟩
    else if hy : x ∈ q.support then iso.toEquiv.symm ⟨x, hy⟩ else x

theorem TameIso.swapMap_of_mem_left (iso : TameIso p q) (x : V)
    (hx : x ∈ p.support) : iso.swapMap x = (iso.toEquiv ⟨x, hx⟩ : V) := by
  classical
  simp only [swapMap, dite_eq_left hx]

theorem TameIso.swapMap_of_mem_right (iso : TameIso p q)
    (hiso : iso.FixesOverlap) (x : V) (hx : x ∈ q.support) :
    iso.swapMap x = (iso.toEquiv.symm ⟨x, hx⟩ : V) := by
  classical
  by_cases hp : x ∈ p.support
  · rw [iso.swapMap_of_mem_left x hp]
    exact (hiso ⟨x, hp⟩ hx).trans ((hiso.symm ⟨x, hx⟩ hp).symm)
  · simp only [swapMap, dite_eq_right hp, dite_eq_left hx]

theorem TameIso.swapMap_of_not_mem (iso : TameIso p q) (x : V)
    (hp : x ∉ p.support) (hq : x ∉ q.support) : iso.swapMap x = x := by
  classical
  simp only [swapMap, dite_eq_right hp, dite_eq_right hq]

theorem TameIso.swapMap_involutive (iso : TameIso p q)
    (hiso : iso.FixesOverlap) : Function.Involutive iso.swapMap := by
  intro x
  by_cases hp : x ∈ p.support
  · rw [iso.swapMap_of_mem_left x hp,
      iso.swapMap_of_mem_right hiso _ (iso.toEquiv ⟨x, hp⟩).property]
    exact congrArg (fun z : p.support => (z : V))
      (iso.toEquiv.symm_apply_apply ⟨x, hp⟩)
  · by_cases hq : x ∈ q.support
    · rw [iso.swapMap_of_mem_right hiso x hq,
        iso.swapMap_of_mem_left _ (iso.toEquiv.symm ⟨x, hq⟩).property]
      exact congrArg (fun z : q.support => (z : V))
        (iso.toEquiv.apply_symm_apply ⟨x, hq⟩)
    · simp only [iso.swapMap_of_not_mem x hp hq]

/-- The canonical involution exchanging an overlap-fixing pair of copies. -/
noncomputable def TameIso.swapExtension (iso : TameIso p q)
    (hiso : iso.FixesOverlap) : V ≃ V where
  toFun := iso.swapMap
  invFun := iso.swapMap
  left_inv := iso.swapMap_involutive hiso
  right_inv := iso.swapMap_involutive hiso

theorem TameIso.swapExtension_of_mem_left (iso : TameIso p q)
    (hiso : iso.FixesOverlap) (x : V) (hx : x ∈ p.support) :
    iso.swapExtension hiso x = (iso.toEquiv ⟨x, hx⟩ : V) :=
  iso.swapMap_of_mem_left x hx

theorem TameIso.swapExtension_of_mem_right (iso : TameIso p q)
    (hiso : iso.FixesOverlap) (x : V) (hx : x ∈ q.support) :
    iso.swapExtension hiso x = (iso.toEquiv.symm ⟨x, hx⟩ : V) :=
  iso.swapMap_of_mem_right hiso x hx

theorem TameIso.swapExtension_of_not_mem (iso : TameIso p q)
    (hiso : iso.FixesOverlap) (x : V) (hp : x ∉ p.support) (hq : x ∉ q.support) :
    iso.swapExtension hiso x = x :=
  iso.swapMap_of_not_mem x hp hq

theorem TameIso.swapExtension_involutive (iso : TameIso p q)
    (hiso : iso.FixesOverlap) : Function.Involutive (iso.swapExtension hiso) :=
  iso.swapMap_involutive hiso

theorem TameIso.swapExtension_symm (iso : TameIso p q)
    (hiso : iso.FixesOverlap) : (iso.swapExtension hiso).symm = iso.swapExtension hiso := rfl

/-- Global block preservation needs no cardinal assumption. -/
theorem TameIso.swapExtension_preservesBlocks (iso : TameIso p q)
    (hiso : iso.FixesOverlap) (hblock : iso.PreservesBlocks) (x : V) :
    block (iso.swapExtension hiso x) = block x := by
  by_cases hp : x ∈ p.support
  · rw [iso.swapExtension_of_mem_left hiso x hp]
    exact hblock ⟨x, hp⟩
  · by_cases hq : x ∈ q.support
    · rw [iso.swapExtension_of_mem_right hiso x hq]
      exact hblock.symm_apply ⟨x, hq⟩
    · rw [iso.swapExtension_of_not_mem hiso x hp hq]

/-- Reversing the recorded copying isomorphism gives the same ambient swap. -/
theorem TameIso.swapExtension_symm_iso (iso : TameIso p q)
    (hiso : iso.FixesOverlap) :
    iso.symm.swapExtension hiso.symm = iso.swapExtension hiso := by
  apply Equiv.ext
  intro x
  by_cases hp : x ∈ p.support
  · rw [iso.symm.swapExtension_of_mem_right hiso.symm x hp,
      iso.swapExtension_of_mem_left hiso x hp]
    rfl
  · by_cases hq : x ∈ q.support
    · rw [iso.symm.swapExtension_of_mem_left hiso.symm x hq,
        iso.swapExtension_of_mem_right hiso x hq]
      rfl
    · rw [iso.symm.swapExtension_of_not_mem hiso.symm x hq hp,
        iso.swapExtension_of_not_mem hiso x hp hq]

theorem TameIso.swapExtension_image_left (iso : TameIso p q)
    (hiso : iso.FixesOverlap) :
    (iso.swapExtension hiso) '' p.support = q.support := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [iso.swapExtension_of_mem_left hiso x hx]
    exact (iso.toEquiv ⟨x, hx⟩).property
  · intro hy
    refine ⟨iso.toEquiv.symm ⟨y, hy⟩, (iso.toEquiv.symm ⟨y, hy⟩).property, ?_⟩
    rw [iso.swapExtension_of_mem_left hiso _ (iso.toEquiv.symm ⟨y, hy⟩).property]
    exact congrArg (fun z : q.support => (z : V))
      (iso.toEquiv.apply_symm_apply ⟨y, hy⟩)

theorem TameIso.swapExtension_image_right (iso : TameIso p q)
    (hiso : iso.FixesOverlap) :
    (iso.swapExtension hiso) '' q.support = p.support := by
  rw [← iso.swapExtension_symm_iso hiso]
  exact iso.symm.swapExtension_image_left hiso.symm

end Erdos1220.BasicCondition

#print axioms Erdos1220.BasicCondition.TameIso.swapExtension
#print axioms Erdos1220.BasicCondition.TameIso.swapExtension_preservesBlocks
#print axioms Erdos1220.BasicCondition.TameIso.swapExtension_symm_iso
