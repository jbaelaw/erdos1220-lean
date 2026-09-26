import Erdos1220.EdgeOrigin

/-!
# A selected ancestor edge is the origin of every blue edge

At unequal birth stages, fold the newer endpoint. At equal positive birth
stages, both endpoints are new and the edge must come from the right copy,
so fold both. The maximum birth ordinal strictly decreases in every recursive
call. Initial vertices have no blue edges.

This origin theorem itself requires no block-preservation assumption. Actual
block preservation is needed later to charge an origin to distinct clique
families without merging their block labels.
-/

open Cardinal Set Order

universe u

namespace Erdos1220.History

open BasicCondition

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

theorem ancestry_head_mem (H : History V I block μ hμ) (x : H.last.support) :
    (H.birth x, (x : V)) ∈ H.ancestry x := by
  classical
  rw [ancestry]
  split <;> simp

theorem ancestry_parent_subset (H : History V I block μ hμ) (x : H.last.support)
    (hx : H.birth x ≠ 0) :
    H.ancestry (H.parentWitness x hx).point ⊆ H.ancestry x := by
  classical
  intro z hz
  rw [ancestry]
  split
  · contradiction
  · exact List.mem_cons_of_mem _ hz

/-- If both endpoints are born at this transition, its new cross edge cannot
join them: one endpoint of that edge must already belong to the left side. -/
theorem ParentWitness.blue_parents_of_birth_eq {H : History V I block μ hμ}
    {x y : H.last.support} (wx : ParentWitness H x) (wy : ParentWitness H y)
    (hxy : H.birth x = H.birth y) (hb : H.last.blue x y) :
    H.last.blue wx.point wy.point := by
  rcases wx with ⟨i, hi, hxbirth, hxn, hxnew, px, hpx⟩
  rcases wy with ⟨j, hj, hybirth, hyn, hynew, py, hpy⟩
  have hij : i = j := by
    apply le_antisymm
    · apply Order.lt_succ_iff.mp
      exact (Order.lt_succ i).trans_eq
        (hxbirth.symm.trans (hxy.trans hybirth))
    · apply Order.lt_succ_iff.mp
      exact (Order.lt_succ j).trans_eq
        (hybirth.symm.trans (hxy.symm.trans hxbirth))
  subst j
  have hi0 : i ≤ H.length := (Order.le_succ i).trans hi
  have hbn : (H.state (Order.succ i) hi).blue x y :=
    ((H.state_extends_last _ hi).2 x hxn y hyn).mp hb
  have hnot : ¬ (H.step i hi).NewEdge x y := by
    rintro ⟨e, _, he⟩
    rcases he with ⟨hx, _⟩ | ⟨_, hy⟩
    · apply hxnew
      rw [hx]
      exact e.left_mem
    · apply hynew
      rw [hy]
      exact e.left_mem
  have hfold := (H.step i hi).fold_blue_of_not_new
    ⟨x, hxn⟩ ⟨y, hyn⟩ hbn hnot
  rw [(H.step i hi).fold_of_new _ hxnew,
    (H.step i hi).fold_of_new _ hynew] at hfold
  rw [← hpx, ← hpy] at hfold
  exact ((H.state_extends_last _ hi0).2 px
    ((H.state i hi0).blue_support hfold).1 py
    ((H.state i hi0).blue_support hfold).2).mpr hfold

/-- Every blue pair traces back to a selected new edge whose endpoints occur
on the two finite ancestry paths. At least one endpoint is born at its stage. -/
theorem blue_has_ancestral_origin (H : History V I block μ hμ)
    (x y : H.last.support) (hb : H.last.blue x y) :
    ∃ z ∈ H.ancestry x, ∃ w ∈ H.ancestry y,
      ∃ i, ∃ hi : Order.succ i ≤ H.length,
        (H.step i hi).NewEdge z.2 w.2 ∧
          (z.1 = Order.succ i ∨ w.1 = Order.succ i) := by
  classical
  rcases lt_trichotomy (H.birth x) (H.birth y) with hxy | hxy | hyx
  · have hyzero : H.birth y ≠ 0 := ne_of_gt (zero_le.trans_lt hxy)
    let wy := H.parentWitness y hyzero
    rcases wy.blue_parent_or_new x hxy (H.last.symmetric hb) with hp | hn
    · obtain ⟨z, hz, w, hw, i, hi, he, hs⟩ :=
        H.blue_has_ancestral_origin x wy.point (H.last.symmetric hp)
      exact ⟨z, hz, w, H.ancestry_parent_subset y hyzero hw, i, hi, he, hs⟩
    · exact ⟨(H.birth x, (x : V)), H.ancestry_head_mem x,
        (H.birth y, (y : V)), H.ancestry_head_mem y,
        wy.index, wy.next_le, (H.step wy.index wy.next_le).newEdge_symm hn,
        Or.inr wy.birth_eq⟩
  · by_cases hxzero : H.birth x = 0
    · have hyzero : H.birth y = 0 := hxy.symm.trans hxzero
      have hx0 := H.mem_state_of_birth_le x 0 zero_le hxzero.le
      have hy0 := H.mem_state_of_birth_le y 0 zero_le hyzero.le
      exact False.elim (H.initial_red x y
        (((H.state_extends_last 0 zero_le).2 x hx0 y hy0).mp hb))
    · have hyzero : H.birth y ≠ 0 := fun hy => hxzero (hxy.trans hy)
      let wx := H.parentWitness x hxzero
      let wy := H.parentWitness y hyzero
      have hp := wx.blue_parents_of_birth_eq wy hxy hb
      obtain ⟨z, hz, w, hw, i, hi, he, hs⟩ :=
        H.blue_has_ancestral_origin wx.point wy.point hp
      exact ⟨z, H.ancestry_parent_subset x hxzero hz,
        w, H.ancestry_parent_subset y hyzero hw, i, hi, he, hs⟩
  · have hxzero : H.birth x ≠ 0 := ne_of_gt (zero_le.trans_lt hyx)
    let wx := H.parentWitness x hxzero
    rcases wx.blue_parent_or_new y hyx hb with hp | hn
    · obtain ⟨z, hz, w, hw, i, hi, he, hs⟩ :=
        H.blue_has_ancestral_origin wx.point y hp
      exact ⟨z, H.ancestry_parent_subset x hxzero hz, w, hw, i, hi, he, hs⟩
    · exact ⟨(H.birth x, (x : V)), H.ancestry_head_mem x,
        (H.birth y, (y : V)), H.ancestry_head_mem y,
        wx.index, wx.next_le, hn, Or.inl wx.birth_eq⟩
termination_by max (H.birth x) (H.birth y)
decreasing_by
  · rw [max_eq_right hxy.le]
    exact max_lt_iff.mpr ⟨hxy, wy.birth_lt⟩
  · rw [hxy, max_self]
    exact max_lt_iff.mpr ⟨wx.birth_lt.trans_eq hxy, wy.birth_lt⟩
  · rw [max_eq_left hyx.le]
    exact max_lt_iff.mpr ⟨wx.birth_lt, hyx⟩

end Erdos1220.History

#print axioms Erdos1220.History.ParentWitness.blue_parents_of_birth_eq
#print axioms Erdos1220.History.blue_has_ancestral_origin
