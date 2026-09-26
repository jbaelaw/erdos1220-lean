import Erdos1220.Ancestry

/-!
# Pure extension and preservation of birth stages

Pure extension preserves the recorded transition data as well as every old
state. Consequently, the first appearance of an old vertex cannot change.
This is required when taking coherent limits of histories.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

structure PureExtends (H K : History V I block μ hμ) : Prop where
  length_le : H.length ≤ K.length
  state_eq : ∀ i (hi : i ≤ H.length), H.state i hi = K.state i (hi.trans length_le)
  step_heq : ∀ i (hi : Order.succ i ≤ H.length),
    HEq (H.step i hi) (K.step i (hi.trans length_le))

theorem pureExtends_refl (H : History V I block μ hμ) : PureExtends H H :=
  ⟨le_rfl, fun _ _ => rfl, fun _ _ => HEq.rfl⟩

theorem PureExtends.trans {H K L : History V I block μ hμ}
    (hHK : PureExtends H K) (hKL : PureExtends K L) : PureExtends H L := by
  refine ⟨hHK.length_le.trans hKL.length_le, ?_, ?_⟩
  · intro i hi
    exact (hHK.state_eq i hi).trans (hKL.state_eq i (hi.trans hHK.length_le))
  · intro i hi
    exact (hHK.step_heq i hi).trans (hKL.step_heq i (hi.trans hHK.length_le))

theorem truncate_pureExtends (H : History V I block μ hμ)
    (δ : Ordinal.{u}) (hδ : δ ≤ H.length) : PureExtends (H.truncate δ hδ) H :=
  ⟨hδ, fun _ _ => rfl, fun _ _ => HEq.rfl⟩

theorem PureExtends.last_extends {H K : History V I block μ hμ}
    (h : PureExtends H K) : Extends H.last K.last := by
  have heq : H.last = K.state H.length h.length_le := h.state_eq H.length le_rfl
  exact (congrArg (fun p => Extends p K.last) heq).mpr
    (K.state_extends_last H.length h.length_le)

def PureExtends.vertex {H K : History V I block μ hμ} (h : PureExtends H K)
    (x : H.last.support) : K.last.support :=
  ⟨x, h.last_extends.1 x.property⟩

theorem PureExtends.birth_vertex_le {H K : History V I block μ hμ}
    (h : PureExtends H K) (x : H.last.support) : K.birth (h.vertex x) ≤ H.birth x := by
  obtain ⟨hb, hx⟩ := H.birth_spec x
  apply K.birth_le (h.vertex x) (H.birth x) (hb.trans h.length_le)
  exact (congrArg (fun p : BasicCondition V I block μ => (x : V) ∈ p.support)
    (h.state_eq (H.birth x) hb)).mp hx

/-- The witness data and entire old prefix remain unchanged, so no old vertex
is moved to a different birth stage by pure extension. -/
theorem PureExtends.birth_vertex {H K : History V I block μ hμ}
    (h : PureExtends H K) (x : H.last.support) : K.birth (h.vertex x) = H.birth x := by
  apply le_antisymm (h.birth_vertex_le x)
  obtain ⟨hk, hxk⟩ := K.birth_spec (h.vertex x)
  obtain ⟨hh, _⟩ := H.birth_spec x
  have hb : K.birth (h.vertex x) ≤ H.length := (h.birth_vertex_le x).trans hh
  apply H.birth_le x (K.birth (h.vertex x)) hb
  exact (congrArg (fun p : BasicCondition V I block μ => (x : V) ∈ p.support)
    (h.state_eq (K.birth (h.vertex x)) hb)).mpr hxk

end Erdos1220.History

#print axioms Erdos1220.History.PureExtends.birth_vertex
