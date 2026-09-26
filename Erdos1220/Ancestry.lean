import Erdos1220.History

/-!
# Terminating ancestry in a recorded history

Every noninitial vertex has the actual preimage supplied by its birth
transition. The birth ordinal strictly decreases at that step. This permits
well-founded recursion to return a finite list, with no artificial depth limit.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.History

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- A parent is tied to the recorded copying map, not merely to an arbitrary
earlier vertex. -/
structure ParentWitness (H : History V I block μ hμ) (x : H.last.support) where
  index : Ordinal.{u}
  next_le : Order.succ index ≤ H.length
  birth_eq : H.birth x = Order.succ index
  at_next : (x : V) ∈ (H.state (Order.succ index) next_le).support
  is_new : (x : V) ∉ (H.state index ((Order.le_succ index).trans next_le)).support
  point : H.last.support
  point_eq : (point : V) =
    ((H.step index next_le).parent ⟨x, at_next⟩ is_new : V)

noncomputable def parentWitness (H : History V I block μ hμ) (x : H.last.support)
    (hzero : H.birth x ≠ 0) : ParentWitness H x := by
  classical
  let hs := (H.birth_zero_or_successor x).resolve_left hzero
  let i := Classical.choose hs
  have hi : Order.succ i = H.birth x := Classical.choose_spec hs
  have hm : Order.succ i ∈ H.appears x :=
    (congrArg (fun β => β ∈ H.appears x) hi).mpr (H.birth_spec x)
  let hb : Order.succ i ≤ H.length := Classical.choose hm
  have hx : (x : V) ∈ (H.state (Order.succ i) hb).support := Classical.choose_spec hm
  let hprev : i ≤ H.length := (Order.le_succ i).trans hb
  have hnew : (x : V) ∉ (H.state i hprev).support :=
    H.not_mem_before_birth x i hprev ((Order.lt_succ i).trans_eq hi)
  let y := (H.step i hb).parent ⟨x, hx⟩ hnew
  have hy : (y : V) ∈ H.last.support := (H.state_extends_last i hprev).1 y.property
  exact {
    index := i
    next_le := hb
    birth_eq := hi.symm
    at_next := hx
    is_new := hnew
    point := ⟨y, hy⟩
    point_eq := rfl }

theorem ParentWitness.birth_lt {H : History V I block μ hμ} {x : H.last.support}
    (w : ParentWitness H x) : H.birth w.point < H.birth x := by
  let hi : w.index ≤ H.length := (Order.le_succ w.index).trans w.next_le
  have hp : (w.point : V) ∈ (H.state w.index hi).support :=
    (congrArg (fun z : V => z ∈ (H.state w.index hi).support) w.point_eq).mpr
      ((H.step w.index w.next_le).parent ⟨x, w.at_next⟩ w.is_new).property
  exact (H.birth_le w.point w.index hi hp).trans_lt
    ((Order.lt_succ w.index).trans_eq w.birth_eq.symm)

open scoped Classical in
/-- The complete backwards path. Lean checks termination by the birth ordinal. -/
noncomputable def ancestry (H : History V I block μ hμ) (x : H.last.support) :
    List (Ordinal.{u} × V) :=
  if hzero : H.birth x = 0 then [(H.birth x, (x : V))]
  else (H.birth x, (x : V)) :: H.ancestry (H.parentWitness x hzero).point
termination_by H.birth x
decreasing_by
  exact (H.parentWitness x hzero).birth_lt

theorem ancestry_ne_nil (H : History V I block μ hμ) (x : H.last.support) :
    H.ancestry x ≠ [] := by
  rw [ancestry]
  split <;> simp

end Erdos1220.History

#print axioms Erdos1220.History.ParentWitness.birth_lt
#print axioms Erdos1220.History.ancestry
