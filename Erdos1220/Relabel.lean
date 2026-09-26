import Erdos1220.BlockPreserving

/-!
# Global relabeling inside blocks

A permutation preserving actual block labels transports colorings,
amalgamations, their recorded witnesses, and whole histories. This is an
algebraic transport result; extending a partial map to such a permutation
remains a separate obligation.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}

/-- The supported permutation, expressed using inverse images. -/
def relabelSupportEquiv (e : V ≃ V) (s : Set V) : s ≃ (e.symm ⁻¹' s) where
  toFun x := ⟨e x, by simpa only [Set.mem_preimage, Equiv.symm_apply_apply] using x.property⟩
  invFun x := ⟨e.symm x, x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)

theorem symm_block (e : V ≃ V) (he : ∀ x, block (e x) = block x) (x : V) :
    block (e.symm x) = block x := by
  simpa only [Equiv.apply_symm_apply] using (he (e.symm x)).symm

def relabel (p : BasicCondition V I block μ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) : BasicCondition V I block μ where
  support := e.symm ⁻¹' p.support
  blue x y := p.blue (e.symm x) (e.symm y)
  symmetric := p.symmetric
  irreflexive x := p.irreflexive (e.symm x)
  blue_support := p.blue_support
  different_blocks := by
    intro x y hxy
    simpa only [symm_block e he] using p.different_blocks hxy
  small := (Cardinal.mk_congr (relabelSupportEquiv e p.support).symm).trans_le p.small

theorem relabel_mem (p : BasicCondition V I block μ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) (x : V) :
    e x ∈ (p.relabel e he).support ↔ x ∈ p.support := by
  simp only [relabel, Set.mem_preimage, Equiv.symm_apply_apply]

theorem relabel_blue (p : BasicCondition V I block μ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) (x y : V) :
    (p.relabel e he).blue (e x) (e y) ↔ p.blue x y := by
  simp only [relabel, Equiv.symm_apply_apply]

def relabelIso (p : BasicCondition V I block μ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) : TameIso p (p.relabel e he) where
  toEquiv := relabelSupportEquiv e p.support
  blue_iff x y := p.relabel_blue e he x y
  block_iff x y := by
    change block (e x) = block (e y) ↔ block x = block y
    rw [he x, he y]

theorem relabelIso_preservesBlocks (p : BasicCondition V I block μ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) : (p.relabelIso e he).PreservesBlocks :=
  fun x => he x

theorem relabel_extends {p q : BasicCondition V I block μ} (hpq : Extends p q)
    (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    Extends (p.relabel e he) (q.relabel e he) := by
  refine ⟨fun _ hx => hpq.1 hx, ?_⟩
  intro x hx y hy
  exact hpq.2 (e.symm x) hx (e.symm y) hy

variable {p q : BasicCondition V I block μ}

/-- Conjugation transports the original support isomorphism. -/
def TameIso.relabel (iso : TameIso p q) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) : TameIso (p.relabel e he) (q.relabel e he) where
  toEquiv := (relabelSupportEquiv e p.support).symm.trans
    (iso.toEquiv.trans (relabelSupportEquiv e q.support))
  blue_iff x y := by
    change q.blue (e.symm (e (iso.toEquiv ⟨e.symm x, x.property⟩)))
      (e.symm (e (iso.toEquiv ⟨e.symm y, y.property⟩))) ↔
      p.blue (e.symm x) (e.symm y)
    simpa only [Equiv.symm_apply_apply] using iso.blue_iff
      ⟨e.symm x, x.property⟩ ⟨e.symm y, y.property⟩
  block_iff x y := by
    change block (e (iso.toEquiv ⟨e.symm x, x.property⟩)) =
      block (e (iso.toEquiv ⟨e.symm y, y.property⟩)) ↔ block x = block y
    rw [he, he]
    exact (iso.block_iff _ _).trans (by rw [symm_block e he, symm_block e he])

theorem TameIso.relabel_preservesBlocks {iso : TameIso p q}
    (hiso : iso.PreservesBlocks) (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (iso.relabel e he).PreservesBlocks := by
  intro x
  change block (e (iso.toEquiv ⟨e.symm x, x.property⟩)) = block x
  rw [he, hiso, symm_block e he]

theorem TameIso.relabel_fixesOverlap {iso : TameIso p q}
    (hiso : iso.FixesOverlap) (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (iso.relabel e he).FixesOverlap := by
  intro x hx
  change e (iso.toEquiv ⟨e.symm x, x.property⟩) = x
  rw [hiso ⟨e.symm x, x.property⟩ hx]
  exact e.apply_symm_apply x

theorem TameIso.relabel_fixesSharedBlocks {iso : TameIso p q}
    (hiso : iso.FixesSharedBlocks) (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (iso.relabel e he).FixesSharedBlocks := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hold : block (e.symm x) ∈ block '' q.support := by
    refine ⟨e.symm y, hy, ?_⟩
    rw [symm_block e he, symm_block e he]
    exact hyx
  change block (e (iso.toEquiv ⟨e.symm x, x.property⟩)) = block x
  rw [he, hiso _ hold, symm_block e he]

theorem TameIso.relabel_symm_apply (iso : TameIso p q) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) (y : q.support) :
    ((iso.relabel e he).toEquiv.symm (relabelSupportEquiv e q.support y) : V) =
      e (iso.toEquiv.symm y) := by
  have h : (relabelSupportEquiv e q.support).symm (relabelSupportEquiv e q.support y) = y :=
    Equiv.symm_apply_apply _ y
  change e (iso.toEquiv.symm ((relabelSupportEquiv e q.support).symm
    (relabelSupportEquiv e q.support y)) : V) = e (iso.toEquiv.symm y)
  rw [h]

def CrossEdge.relabel (a : CrossEdge p q) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) : CrossEdge (p.relabel e he) (q.relabel e he) where
  left := e a.left
  right := e a.right
  left_mem := (p.relabel_mem e he a.left).mpr a.left_mem
  left_not_mem h := a.left_not_mem ((q.relabel_mem e he a.left).mp h)
  right_mem := (q.relabel_mem e he a.right).mpr a.right_mem
  right_not_mem h := a.right_not_mem ((p.relabel_mem e he a.right).mp h)
  block_ne := by simpa only [he] using a.block_ne

theorem CrossEdge.relabel_adj (a : CrossEdge p q) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) (x y : V) :
    (a.relabel e he).Adj x y ↔ a.Adj (e.symm x) (e.symm y) := by
  simp only [CrossEdge.Adj, CrossEdge.relabel, Equiv.symm_apply_eq]

theorem CrossEdge.relabel_sourceSeparated (a : CrossEdge p q) (iso : TameIso p q)
    (ha : a.SourceSeparated iso) (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (a.relabel e he).SourceSeparated (iso.relabel e he) := by
  change block (e a.left) ≠ block
    ((iso.relabel e he).toEquiv.symm
      (relabelSupportEquiv e q.support ⟨a.right, a.right_mem⟩))
  rw [iso.relabel_symm_apply, he, he]
  exact ha

/-- Equality of the mathematical fields determines a basic condition. -/
theorem eq_of_support_blue {p q : BasicCondition V I block μ}
    (hs : p.support = q.support) (hb : ∀ x y, p.blue x y ↔ q.blue x y) : p = q := by
  cases p with
  | mk sp bp symp irp suppp dbp smallp =>
    cases q with
    | mk sq bq symq irq suppq dbq smallq =>
      cases hs
      have hblue : bp = bq := funext fun x => funext fun y => propext (hb x y)
      cases hblue
      rfl

/-- A global extension of a support isomorphism sends the entire condition
exactly onto its target, including colors outside the support. -/
theorem relabel_eq_of_iso (iso : TameIso p q) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x)
    (hext : ∀ x : p.support, e x = (iso.toEquiv x : V)) : p.relabel e he = q := by
  have hinv : ∀ y : q.support, e.symm y = (iso.toEquiv.symm y : V) := by
    intro y
    apply e.injective
    rw [e.apply_symm_apply, hext]
    exact (congrArg (fun z : q.support => (z : V)) (iso.toEquiv.apply_symm_apply y)).symm
  apply eq_of_support_blue
  · ext x
    constructor
    · intro hx
      have hqx := (iso.toEquiv ⟨e.symm x, hx⟩).property
      simpa only [← hext, Equiv.apply_symm_apply] using hqx
    · intro hx
      change e.symm x ∈ p.support
      rw [hinv ⟨x, hx⟩]
      exact (iso.toEquiv.symm ⟨x, hx⟩).property
  · intro x y
    constructor
    · intro hxy
      obtain ⟨hx, hy⟩ := p.blue_support hxy
      have hq := (iso.blue_iff ⟨e.symm x, hx⟩ ⟨e.symm y, hy⟩).mpr hxy
      simpa only [← hext, Equiv.apply_symm_apply] using hq
    · intro hxy
      obtain ⟨hx, hy⟩ := q.blue_support hxy
      change p.blue (e.symm x) (e.symm y)
      rw [hinv ⟨x, hx⟩, hinv ⟨y, hy⟩]
      apply (iso.blue_iff (iso.toEquiv.symm ⟨x, hx⟩) (iso.toEquiv.symm ⟨y, hy⟩)).mp
      simpa only [Equiv.apply_symm_apply] using hxy

theorem relabel_redAmalgam (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (redAmalgam p q hμ).relabel e he = redAmalgam (p.relabel e he) (q.relabel e he) hμ :=
  eq_of_support_blue rfl (fun _ _ => Iff.rfl)

theorem relabel_blueAmalgam (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (a : CrossEdge p q) (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (blueAmalgam p q hμ a).relabel e he =
      blueAmalgam (p.relabel e he) (q.relabel e he) hμ (a.relabel e he) := by
  refine eq_of_support_blue rfl (fun x y => ?_)
  exact or_congr Iff.rfl (a.relabel_adj e he x y).symm

theorem relabel_amalgamResult (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (a : Option (CrossEdge p q)) (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (amalgamResult p q hμ a).relabel e he =
      amalgamResult (p.relabel e he) (q.relabel e he) hμ
        (a.map fun b => b.relabel e he) := by
  cases a with
  | none => exact relabel_redAmalgam p q hμ e he
  | some a => exact relabel_blueAmalgam p q hμ a e he

namespace Transition

variable {hμ : ℵ₀ ≤ μ} {r : BasicCondition V I block μ}

/-- The transition keeps its original witnesses, transported by conjugation. -/
def relabel (t : Transition hμ p r) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) : Transition hμ (p.relabel e he) (r.relabel e he) where
  right := t.right.relabel e he
  iso := t.iso.relabel e he
  fixesOverlap := TameIso.relabel_fixesOverlap t.fixesOverlap e he
  fixesSharedBlocks := TameIso.relabel_fixesSharedBlocks t.fixesSharedBlocks e he
  edge := t.edge.map fun a => a.relabel e he
  sourceSeparated := by
    intro a ha
    cases ht : t.edge with
    | none => simp only [ht, Option.map_none, reduceCtorEq] at ha
    | some b =>
      simp only [ht, Option.map_some, Option.some.injEq] at ha
      subst a
      exact b.relabel_sourceSeparated t.iso (t.sourceSeparated b ht) e he
  result_eq := (congrArg (fun s : BasicCondition V I block μ => s.relabel e he)
    t.result_eq).trans (relabel_amalgamResult p t.right hμ t.edge e he)

theorem relabel_preservesBlocks (t : Transition hμ p r) (ht : t.iso.PreservesBlocks)
    (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (t.relabel e he).iso.PreservesBlocks := TameIso.relabel_preservesBlocks ht e he

end Transition
end Erdos1220.BasicCondition

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- Relabel every state and every recorded transition, preserving continuity. -/
def relabel (H : History V I block μ hμ) (e : V ≃ V)
    (he : ∀ x, block (e x) = block x) : History V I block μ hμ where
  length := H.length
  length_lt := H.length_lt
  state i hi := (H.state i hi).relabel e he
  increasing i j hi hj hij := relabel_extends (H.increasing i j hi hj hij) e he
  initial_red x y := H.initial_red (e.symm x) (e.symm y)
  initial_block_injective := by
    intro x hx y hy hxy
    apply e.symm.injective
    apply H.initial_block_injective (e.symm x) hx (e.symm y) hy
    simpa only [symm_block e he] using hxy
  initial_nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := H.initial_nontrivial
    exact ⟨e x, ((H.state 0 zero_le).relabel_mem e he x).mpr hx,
      e y, ((H.state 0 zero_le).relabel_mem e he y).mpr hy,
      fun h => hxy (e.injective h)⟩
  step i hi := (H.step i hi).relabel e he
  limit_support i hi hlim x := H.limit_support i hi hlim (e.symm x)
  limit_blue i hi hlim x y := H.limit_blue i hi hlim (e.symm x) (e.symm y)

theorem relabel_blockPreserving {H : History V I block μ hμ}
    (hH : H.BlockPreserving) (e : V ≃ V) (he : ∀ x, block (e x) = block x) :
    (H.relabel e he).BlockPreserving :=
  fun i hi => (H.step i hi).relabel_preservesBlocks (hH i hi) e he

end Erdos1220.History

#print axioms Erdos1220.BasicCondition.Transition.relabel
#print axioms Erdos1220.History.relabel
#print axioms Erdos1220.History.relabel_blockPreserving
