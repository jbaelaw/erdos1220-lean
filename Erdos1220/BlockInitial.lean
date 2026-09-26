import Erdos1220.HistoryConstruction
import Erdos1220.BlockPreserving

/-!
# An initial history meeting every block

A section of the block map gives an all-red condition with exactly one
representative per block. If there are at least two blocks and at most `μ`
blocks, this is a valid initial history. Its length is zero, so its
block-preservation condition holds without any successor transitions.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}

/-- The all-red condition supported on a section of the block map. -/
def blockSection (rep : I → V) (hrep : ∀ i, block (rep i) = i) (hI : #I ≤ μ) :
    BasicCondition V I block μ where
  support := Set.range rep
  blue _ _ := False
  symmetric := False.elim
  irreflexive := fun _ => id
  blue_support := False.elim
  different_blocks := False.elim
  small := by
    have hinj : Function.Injective rep :=
      (show Function.LeftInverse block rep from hrep).injective
    rw [Cardinal.mk_range_eq rep hinj]
    exact hI

theorem blockSection_injective (rep : I → V) (hrep : ∀ i, block (rep i) = i)
    (hI : #I ≤ μ) :
    ∀ x ∈ (blockSection rep hrep hI).support,
      ∀ y ∈ (blockSection rep hrep hI).support, block x = block y → x = y := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  exact congrArg rep ((hrep i).symm.trans (hij.trans (hrep j)))

theorem blockSection_nontrivial [Nontrivial I] (rep : I → V)
    (hrep : ∀ i, block (rep i) = i) (hI : #I ≤ μ) :
    ∃ x ∈ (blockSection rep hrep hI).support,
      ∃ y ∈ (blockSection rep hrep hI).support, x ≠ y := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  refine ⟨rep i, ⟨i, rfl⟩, rep j, ⟨j, rfl⟩, ?_⟩
  intro heq
  exact hij ((hrep i).symm.trans ((congrArg block heq).trans (hrep j)))

theorem blockSection_covers (rep : I → V) (hrep : ∀ i, block (rep i) = i)
    (hI : #I ≤ μ) (i : I) :
    ∃ x ∈ (blockSection rep hrep hI).support, block x = i :=
  ⟨rep i, ⟨i, rfl⟩, hrep i⟩

end Erdos1220.BasicCondition

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- A valid initial history with one point in every block. -/
def ofBlockSection [Nontrivial I] (rep : I → V)
    (hrep : ∀ i, block (rep i) = i) (hI : #I ≤ μ) : History V I block μ hμ :=
  ofInitial (blockSection rep hrep hI) (fun _ _ => id)
    (blockSection_injective rep hrep hI) (blockSection_nontrivial rep hrep hI)

@[simp] theorem ofBlockSection_length [Nontrivial I] (rep : I → V)
    (hrep : ∀ i, block (rep i) = i) (hI : #I ≤ μ) :
    (ofBlockSection (hμ := hμ) rep hrep hI).length = 0 := rfl

@[simp] theorem ofBlockSection_last [Nontrivial I] (rep : I → V)
    (hrep : ∀ i, block (rep i) = i) (hI : #I ≤ μ) :
    (ofBlockSection (hμ := hμ) rep hrep hI).last = blockSection rep hrep hI := rfl

theorem ofBlockSection_blockPreserving [Nontrivial I] (rep : I → V)
    (hrep : ∀ i, block (rep i) = i) (hI : #I ≤ μ) :
    (ofBlockSection (hμ := hμ) rep hrep hI).BlockPreserving := by
  intro i hi
  change Order.succ i ≤ (0 : Ordinal.{u}) at hi
  exact False.elim ((Order.lt_succ i).not_ge (hi.trans bot_le))

theorem ofBlockSection_covers [Nontrivial I] (rep : I → V)
    (hrep : ∀ i, block (rep i) = i) (hI : #I ≤ μ) (i : I) :
    ∃ x ∈ (ofBlockSection (hμ := hμ) rep hrep hI).last.support, block x = i :=
  blockSection_covers rep hrep hI i

/-- The block-preserving history class contains a history meeting every
block; this proves nonemptiness of that class, not a density theorem. -/
theorem exists_blockPreserving_cover [Nontrivial I] (rep : I → V)
    (hrep : ∀ i, block (rep i) = i) (hI : #I ≤ μ) :
    ∃ H : History V I block μ hμ, H.BlockPreserving ∧
      ∀ i : I, ∃ x ∈ H.last.support, block x = i :=
  ⟨ofBlockSection rep hrep hI, ofBlockSection_blockPreserving rep hrep hI,
    ofBlockSection_covers rep hrep hI⟩

end Erdos1220.History

#print axioms Erdos1220.History.exists_blockPreserving_cover
