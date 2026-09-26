import Erdos1220.Folding
import Mathlib.Order.WellFounded

/-!
# Explicit ordinal histories

Successor steps retain their actual copying isomorphism. Limit steps retain
the union of both supports and colors. No assertion about clique exclusion is
part of the definition.

This candidate construction explicitly imposes source-block separation on a
new blue edge. Its closure, chain condition, and final forcing claims remain
separate proof obligations; they cannot be inferred just from this definition.
-/

open Cardinal Set Order

universe u

namespace Erdos1220
namespace BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}}

def amalgamResult (p q : BasicCondition V I block μ) (hμ : ℵ₀ ≤ μ)
    (edge : Option (CrossEdge p q)) : BasicCondition V I block μ :=
  match edge with
  | none => redAmalgam p q hμ
  | some e => blueAmalgam p q hμ e

/-- A concrete successor construction, including the data needed to trace copies. -/
structure Transition (hμ : ℵ₀ ≤ μ) (p r : BasicCondition V I block μ) where
  right : BasicCondition V I block μ
  iso : TameIso p right
  fixesOverlap : iso.FixesOverlap
  fixesSharedBlocks : iso.FixesSharedBlocks
  edge : Option (CrossEdge p right)
  sourceSeparated : ∀ e, edge = some e → e.SourceSeparated iso
  result_eq : r = amalgamResult p right hμ edge

namespace Transition

variable {hμ : ℵ₀ ≤ μ} {p r : BasicCondition V I block μ}

theorem support_eq (t : Transition hμ p r) : r.support = p.support ∪ t.right.support := by
  calc
    r.support = (amalgamResult p t.right hμ t.edge).support :=
      congrArg BasicCondition.support t.result_eq
    _ = p.support ∪ t.right.support := by cases t.edge <;> rfl

theorem extends_left (t : Transition hμ p r) : Extends p r := by
  have h : Extends p (amalgamResult p t.right hμ t.edge) := by
    cases t.edge with
    | none =>
      exact extends_redAmalgam_left p t.right hμ (t.iso.agreeOnOverlap t.fixesOverlap)
    | some e =>
      exact extends_blueAmalgam_left p t.right hμ
        (t.iso.agreeOnOverlap t.fixesOverlap) e
  exact (congrArg (fun s => Extends p s) t.result_eq).mpr h

/-- A genuinely new vertex comes from the right-hand copy. -/
noncomputable def parent (t : Transition hμ p r) (x : r.support)
    (hx : (x : V) ∉ p.support) : p.support :=
  t.iso.toEquiv.symm ⟨x, by
    have h : (x : V) ∈ p.support ∪ t.right.support :=
      (congrArg (fun s : Set V => (x : V) ∈ s) t.support_eq).mp x.property
    exact h.resolve_left hx⟩

theorem parent_maps_to (t : Transition hμ p r) (x : r.support)
    (hx : (x : V) ∉ p.support) : (t.iso.toEquiv (t.parent x hx) : V) = x := by
  simp only [parent, Equiv.apply_symm_apply]

end Transition
end BasicCondition

open BasicCondition

/-- A history records witnesses rather than assuming that an amalgamation
isomorphism is uniquely recoverable from the last graph. -/
structure History (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) where
  length : Ordinal.{u}
  length_lt : length < (Order.succ μ).ord
  state : ∀ i : Ordinal.{u}, i ≤ length → BasicCondition V I block μ
  increasing : ∀ i j (hi : i ≤ length) (hj : j ≤ length), i ≤ j →
    Extends (state i hi) (state j hj)
  initial_red : ∀ x y, ¬ (state 0 zero_le).blue x y
  initial_block_injective : ∀ x ∈ (state 0 zero_le).support,
    ∀ y ∈ (state 0 zero_le).support, block x = block y → x = y
  initial_nontrivial : ∃ x ∈ (state 0 zero_le).support,
    ∃ y ∈ (state 0 zero_le).support, x ≠ y
  step : ∀ i (hi : Order.succ i ≤ length),
    Transition hμ (state i ((Order.le_succ i).trans hi)) (state (Order.succ i) hi)
  limit_support : ∀ i (hi : i ≤ length), Order.IsSuccLimit i → ∀ x,
    x ∈ (state i hi).support ↔
      ∃ j, ∃ hji : j < i, x ∈ (state j (hji.le.trans hi)).support
  limit_blue : ∀ i (hi : i ≤ length), Order.IsSuccLimit i → ∀ x y,
    (state i hi).blue x y ↔
      ∃ j, ∃ hji : j < i, (state j (hji.le.trans hi)).blue x y

namespace History

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

def last (H : History V I block μ hμ) : BasicCondition V I block μ :=
  H.state H.length le_rfl

/-- Truncation keeps the actual transition witnesses. -/
def truncate (H : History V I block μ hμ) (δ : Ordinal.{u}) (hδ : δ ≤ H.length) :
    History V I block μ hμ where
  length := δ
  length_lt := hδ.trans_lt H.length_lt
  state i hi := H.state i (hi.trans hδ)
  increasing i j hi hj hij := H.increasing i j (hi.trans hδ) (hj.trans hδ) hij
  initial_red := H.initial_red
  initial_block_injective := H.initial_block_injective
  initial_nontrivial := H.initial_nontrivial
  step i hi := H.step i (hi.trans hδ)
  limit_support i hi hlim x := H.limit_support i (hi.trans hδ) hlim x
  limit_blue i hi hlim x y := H.limit_blue i (hi.trans hδ) hlim x y

theorem state_extends_last (H : History V I block μ hμ) (i : Ordinal.{u})
    (hi : i ≤ H.length) : Extends (H.state i hi) H.last :=
  H.increasing i H.length hi le_rfl hi

def appears (H : History V I block μ hμ) (x : H.last.support) : Set Ordinal.{u} :=
  {i | ∃ hi : i ≤ H.length, (x : V) ∈ (H.state i hi).support}

theorem appears_nonempty (H : History V I block μ hμ) (x : H.last.support) :
    (H.appears x).Nonempty := ⟨H.length, le_rfl, x.property⟩

noncomputable def birth (H : History V I block μ hμ) (x : H.last.support) : Ordinal.{u} :=
  Ordinal.lt_wf.min (H.appears x) (H.appears_nonempty x)

theorem birth_spec (H : History V I block μ hμ) (x : H.last.support) :
    ∃ hi : H.birth x ≤ H.length, (x : V) ∈ (H.state (H.birth x) hi).support := by
  change H.birth x ∈ H.appears x
  exact Ordinal.lt_wf.min_mem (H.appears x) (H.appears_nonempty x)

theorem birth_le (H : History V I block μ hμ) (x : H.last.support)
    (i : Ordinal.{u}) (hi : i ≤ H.length) (hx : (x : V) ∈ (H.state i hi).support) :
    H.birth x ≤ i :=
  Ordinal.lt_wf.min_le (show i ∈ H.appears x from ⟨hi, hx⟩)

theorem not_mem_before_birth (H : History V I block μ hμ) (x : H.last.support)
    (i : Ordinal.{u}) (hi : i ≤ H.length) (hlt : i < H.birth x) :
    (x : V) ∉ (H.state i hi).support :=
  fun hx => (H.birth_le x i hi hx).not_gt hlt

/-- Limit stages introduce no new vertices, so a birth stage cannot be a limit. -/
theorem birth_not_limit (H : History V I block μ hμ) (x : H.last.support) :
    ¬ Order.IsSuccLimit (H.birth x) := by
  intro hlim
  obtain ⟨hi, hx⟩ := H.birth_spec x
  obtain ⟨j, hji, hjx⟩ := (H.limit_support _ hi hlim x).mp hx
  exact H.not_mem_before_birth x j (hji.le.trans hi) hji hjx

theorem birth_zero_or_successor (H : History V I block μ hμ) (x : H.last.support) :
    H.birth x = 0 ∨ ∃ i, Order.succ i = H.birth x := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit (H.birth x) with hzero | hsucc | hlim
  · exact Or.inl hzero
  · exact Or.inr hsucc
  · exact False.elim (H.birth_not_limit x hlim)

end History
end Erdos1220

#print axioms Erdos1220.History.birth_zero_or_successor
