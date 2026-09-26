import Erdos1220.BlockPreserving

/-!
# Finitely many event blocks along an ancestry path

Each successor transition records at most one new edge and therefore two
endpoint blocks. A finite ancestry path encounters only finitely many such
blocks. These are actual events, not an assumed sparsity condition.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.BasicCondition.Transition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}
variable {p r : BasicCondition V I block μ}

def eventBlocks (t : Transition hμ p r) : Set I :=
  {b | ∃ e, t.edge = some e ∧ (b = block e.left ∨ b = block e.right)}

theorem finite_eventBlocks (t : Transition hμ p r) : t.eventBlocks.Finite := by
  cases he : t.edge with
  | none => simp [eventBlocks, he]
  | some e =>
    have heq : t.eventBlocks = {block e.left, block e.right} := by
      ext b
      simp [eventBlocks, he]
    rw [heq]
    simp

theorem newEdge_mem_eventBlocks (t : Transition hμ p r) {x y : V}
    (h : t.NewEdge x y) : block x ∈ t.eventBlocks ∧ block y ∈ t.eventBlocks := by
  obtain ⟨e, he, hxy⟩ := h
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨e, he, Or.inl rfl⟩, ⟨e, he, Or.inr rfl⟩⟩
  · exact ⟨⟨e, he, Or.inr rfl⟩, ⟨e, he, Or.inl rfl⟩⟩

end Erdos1220.BasicCondition.Transition

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

def stageEventBlocks (H : History V I block μ hμ) (s : Ordinal.{u}) : Set I :=
  {b | ∃ i, ∃ hi : Order.succ i ≤ H.length,
    s = Order.succ i ∧ b ∈ (H.step i hi).eventBlocks}

theorem finite_stageEventBlocks (H : History V I block μ hμ) (s : Ordinal.{u}) :
    (H.stageEventBlocks s).Finite := by
  classical
  by_cases hs : ∃ i, s = Order.succ i ∧ Order.succ i ≤ H.length
  · obtain ⟨i, hsi, hi⟩ := hs
    have heq : H.stageEventBlocks s = (H.step i hi).eventBlocks := by
      ext b
      constructor
      · rintro ⟨j, hj, hsj, hb⟩
        have hji : j = i := Order.succ_injective (hsj.symm.trans hsi)
        subst j
        exact hb
      · intro hb
        exact ⟨i, hi, hsi, hb⟩
    rw [heq]
    exact (H.step i hi).finite_eventBlocks
  · have heq : H.stageEventBlocks s = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro b ⟨i, hi, hsi, _⟩
      exact hs ⟨i, hsi, hi⟩
    rw [heq]
    exact Set.finite_empty

def pathEventBlocks (H : History V I block μ hμ) (l : List (Ordinal.{u} × V)) : Set I :=
  {b | ∃ z ∈ l, b ∈ H.stageEventBlocks z.1}

theorem finite_pathEventBlocks (H : History V I block μ hμ)
    (l : List (Ordinal.{u} × V)) : (H.pathEventBlocks l).Finite := by
  induction l with
  | nil => simp [pathEventBlocks]
  | cons z l ih =>
    have heq : H.pathEventBlocks (z :: l) = H.stageEventBlocks z.1 ∪ H.pathEventBlocks l := by
      ext b
      simp only [pathEventBlocks, Set.mem_ofPred_eq, List.mem_cons, Set.mem_union]
      aesop
    rw [heq]
    exact (H.finite_stageEventBlocks z.1).union ih

def ancestralEventBlocks (H : History V I block μ hμ) (x : H.last.support) : Set I :=
  H.pathEventBlocks (H.ancestry x)

theorem finite_ancestralEventBlocks (H : History V I block μ hμ) (x : H.last.support) :
    (H.ancestralEventBlocks x).Finite := H.finite_pathEventBlocks _

theorem mem_ancestralEventBlocks (H : History V I block μ hμ) (x : H.last.support)
    (z : Ordinal.{u} × V) (hz : z ∈ H.ancestry x) (i : Ordinal.{u})
    (hi : Order.succ i ≤ H.length) (hzi : z.1 = Order.succ i)
    {b : I} (hb : b ∈ (H.step i hi).eventBlocks) : b ∈ H.ancestralEventBlocks x :=
  ⟨z, hz, i, hi, hzi, hb⟩

end Erdos1220.History

#print axioms Erdos1220.History.finite_ancestralEventBlocks
