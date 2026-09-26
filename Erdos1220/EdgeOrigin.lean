import Erdos1220.Ancestry

/-!
# Tracing a blue edge through its birth transition

A successor transition introduces at most its recorded single cross edge.
Every other blue edge folds to an earlier blue edge. These statements use the
actual recorded map, rather than treating a parent as an arbitrary old point.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.BasicCondition.Transition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}
variable {p r : BasicCondition V I block μ}

def NewEdge (t : Transition hμ p r) (x y : V) : Prop :=
  ∃ e, t.edge = some e ∧ e.Adj x y

theorem blue_iff (t : Transition hμ p r) (x y : V) :
    r.blue x y ↔ p.blue x y ∨ t.right.blue x y ∨ t.NewEdge x y := by
  have hr : r.blue x y = (amalgamResult p t.right hμ t.edge).blue x y :=
    congrArg (fun s : BasicCondition V I block μ => s.blue x y) t.result_eq
  rw [hr]
  cases he : t.edge with
  | none => simp [amalgamResult, redAmalgam, NewEdge, he]
  | some e => simp [amalgamResult, blueAmalgam, redAmalgam, NewEdge, he, or_assoc]

theorem newEdge_symm (t : Transition hμ p r) {x y : V}
    (h : t.NewEdge x y) : t.NewEdge y x := by
  obtain ⟨e, he, hxy⟩ := h
  exact ⟨e, he, e.adj_symm hxy⟩

theorem newEdge_unique (t : Transition hμ p r) {x y z w : V}
    (hxy : t.NewEdge x y) (hzw : t.NewEdge z w) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  obtain ⟨e, he, hxy⟩ := hxy
  obtain ⟨f, hf, hzw⟩ := hzw
  have hef : e = f := Option.some.inj (he.symm.trans hf)
  subst f
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

noncomputable def fold (t : Transition hμ p r) (x : r.support) : p.support :=
  t.iso.fold ⟨x, (congrArg (fun s : Set V => (x : V) ∈ s) t.support_eq).mp x.property⟩

theorem fold_of_old (t : Transition hμ p r) (x : r.support)
    (hx : (x : V) ∈ p.support) : t.fold x = ⟨x, hx⟩ :=
  t.iso.fold_of_left _ hx

theorem fold_of_new (t : Transition hμ p r) (x : r.support)
    (hx : (x : V) ∉ p.support) : t.fold x = t.parent x hx := by
  classical
  simp only [fold, TameIso.fold, dite_eq_right hx, parent]

theorem fold_blue_of_not_new (t : Transition hμ p r) (x y : r.support)
    (hb : r.blue x y) (hn : ¬ t.NewEdge x y) : p.blue (t.fold x) (t.fold y) := by
  have hi : (redAmalgam p t.right hμ).blue x y := by
    rcases (t.blue_iff x y).mp hb with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn h)
  exact t.iso.fold_inherited_blue t.fixesOverlap hμ _ _ hi

theorem parent_blue_or_new (t : Transition hμ p r) (x y : r.support)
    (hx : (x : V) ∉ p.support) (hy : (y : V) ∈ p.support)
    (hb : r.blue x y) : p.blue (t.parent x hx) y ∨ t.NewEdge x y := by
  classical
  by_cases hn : t.NewEdge x y
  · exact Or.inr hn
  · have h := t.fold_blue_of_not_new x y hb hn
    rw [t.fold_of_new x hx, t.fold_of_old y hy] at h
    exact Or.inl h

end Erdos1220.BasicCondition.Transition

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

theorem mem_state_of_birth_le (H : History V I block μ hμ) (x : H.last.support)
    (i : Ordinal.{u}) (hi : i ≤ H.length) (hb : H.birth x ≤ i) :
    (x : V) ∈ (H.state i hi).support := by
  obtain ⟨hb', hx⟩ := H.birth_spec x
  exact (H.increasing _ i hb' hi hb).1 hx

/-- An edge to an older point either survives to the actual parent or is the
single cross edge introduced at this birth stage. -/
theorem ParentWitness.blue_parent_or_new {H : History V I block μ hμ}
    {x : H.last.support} (w : ParentWitness H x) (y : H.last.support)
    (hby : H.birth y < H.birth x) (hb : H.last.blue x y) :
    H.last.blue w.point y ∨ (H.step w.index w.next_le).NewEdge x y := by
  have hyi : H.birth y ≤ w.index := by
    rw [w.birth_eq] at hby
    exact Order.lt_succ_iff.mp hby
  have hi : w.index ≤ H.length := (Order.le_succ w.index).trans w.next_le
  have hyp := H.mem_state_of_birth_le y w.index hi hyi
  have hyn := (H.increasing _ _ hi w.next_le (Order.le_succ w.index)).1 hyp
  have hbn : (H.state (Order.succ w.index) w.next_le).blue x y :=
    ((H.state_extends_last _ w.next_le).2 x w.at_next y hyn).mp hb
  rcases (H.step w.index w.next_le).parent_blue_or_new
      ⟨x, w.at_next⟩ ⟨y, hyn⟩ w.is_new hyp hbn with h | h
  · left
    rw [← w.point_eq] at h
    exact ((H.state_extends_last _ hi).2 w.point
      ((H.state w.index hi).blue_support h).1 y hyp).mpr h
  · exact Or.inr h

end Erdos1220.History

#print axioms Erdos1220.BasicCondition.Transition.newEdge_unique
#print axioms Erdos1220.History.ParentWitness.blue_parent_or_new
