import Erdos1220.BlockPreserving

/-! Algebraic symmetry needed to regard either input of an amalgamation as
the current history branch. This file does not define the full weak order. -/

open Cardinal Set Order

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

@[ext] theorem ext {p q : BasicCondition V I block μ}
    (hs : p.support = q.support) (hb : ∀ x y, p.blue x y ↔ q.blue x y) : p = q := by
  cases p with
  | mk ps pb psy pi psup pdiff psmall =>
    cases q with
    | mk qs qb qsy qi qsup qdiff qsmall =>
      dsimp at hs hb
      have hblue : pb = qb := funext fun x => funext fun y => propext (hb x y)
      cases hs
      cases hblue
      rfl

variable {p q : BasicCondition V I block μ}

def TameIso.symm (iso : TameIso p q) : TameIso q p where
  toEquiv := iso.toEquiv.symm
  blue_iff x y := by
    simpa only [Equiv.apply_symm_apply] using
      (iso.blue_iff (iso.toEquiv.symm x) (iso.toEquiv.symm y)).symm
  block_iff x y := by
    simpa only [Equiv.apply_symm_apply] using
      (iso.block_iff (iso.toEquiv.symm x) (iso.toEquiv.symm y)).symm

theorem TameIso.FixesOverlap.symm {iso : TameIso p q}
    (h : iso.FixesOverlap) : iso.symm.FixesOverlap := by
  intro y hy
  have heq : iso.toEquiv ⟨y, hy⟩ = y := Subtype.ext (h ⟨y, hy⟩ y.property)
  exact congrArg (fun z : p.support => (z : V))
    ((congrArg iso.toEquiv.symm heq).symm.trans (iso.toEquiv.symm_apply_apply _))

theorem TameIso.PreservesBlocks.symm {iso : TameIso p q}
    (h : iso.PreservesBlocks) : iso.symm.PreservesBlocks := h.symm_apply

def CrossEdge.swap (e : CrossEdge p q) : CrossEdge q p where
  left := e.right
  right := e.left
  left_mem := e.right_mem
  left_not_mem := e.right_not_mem
  right_mem := e.left_mem
  right_not_mem := e.left_not_mem
  block_ne := e.block_ne.symm

theorem CrossEdge.swap_adj_iff (e : CrossEdge p q) (x y : V) :
    e.swap.Adj x y ↔ e.Adj x y := by
  exact or_comm

theorem redAmalgam_comm (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ) :
    redAmalgam p q hμ = redAmalgam q p hμ := by
  apply ext (Set.union_comm _ _)
  intro x y
  exact or_comm

theorem blueAmalgam_comm (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (e : CrossEdge p q) : blueAmalgam p q hμ e = blueAmalgam q p hμ e.swap := by
  apply ext (Set.union_comm _ _)
  intro x y
  change (p.blue x y ∨ q.blue x y) ∨ e.Adj x y ↔
    (q.blue x y ∨ p.blue x y) ∨ e.swap.Adj x y
  rw [e.swap_adj_iff]
  exact or_congr or_comm Iff.rfl

namespace Transition

variable {r : BasicCondition V I block μ}

def cast {p' r' : BasicCondition V I block μ} (t : Transition hμ p r)
    (hp : p = p') (hr : r = r') : Transition hμ p' r' := by
  subst p'
  subst r'
  exact t

theorem cast_heq {p' r' : BasicCondition V I block μ} (t : Transition hμ p r)
    (hp : p = p') (hr : r = r') : HEq (t.cast hp hr) t := by
  subst p'
  subst r'
  rfl

/-- A label-preserving step can be viewed from its right-hand copy. -/
def reverse (t : Transition hμ p r) (ht : t.iso.PreservesBlocks) :
    Transition hμ t.right r where
  right := p
  iso := t.iso.symm
  fixesOverlap := t.fixesOverlap.symm
  fixesSharedBlocks := ht.symm.fixesSharedBlocks
  edge := t.edge.map CrossEdge.swap
  sourceSeparated := by
    intro e _he
    exact e.sourceSeparated_of_preservesBlocks t.iso.symm ht.symm
  result_eq := by
    calc
      r = amalgamResult p t.right hμ t.edge := t.result_eq
      _ = amalgamResult t.right p hμ (t.edge.map CrossEdge.swap) := by
        cases he : t.edge with
        | none => exact redAmalgam_comm p t.right hμ
        | some e => exact blueAmalgam_comm p t.right hμ e

theorem reverse_preservesBlocks (t : Transition hμ p r) (ht : t.iso.PreservesBlocks) :
    (t.reverse ht).iso.PreservesBlocks := ht.symm

end Transition
end Erdos1220.BasicCondition

#print axioms Erdos1220.BasicCondition.Transition.reverse
