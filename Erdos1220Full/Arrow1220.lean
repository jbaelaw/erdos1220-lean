/-
# Erdős #1220 — colourings of `[λ]²` in `ZFSet.{0}` versus Mathlib's `PairArrow`

For a `ZFSet` `L` all of whose elements are ordinals, the set-theoretic partition statement
(colourings are sets of pairs `((α, β), i)`, `α ∈ β ∈ L`, `i ∈ {0, 1}`) is equivalent to
`Erdos1220.PairArrow (card L) α β` (colourings of two-element `Finset`s of any type of
cardinality `card L`).
-/
import Erdos1220Full.Card1220

open Cardinal

namespace Erdos1220.FOL

/-- The set-theoretic partition relation with cardinal targets. -/
def SemArrow (L : ZFSet.{0}) (α β : Cardinal.{0}) : Prop :=
  ∀ c : ZFSet.{0}, ColZ L c →
    (∃ H : ZFSet.{0}, SubZ H L ∧ ZFSet.card H = α ∧ Hom0Z c H) ∨
    (∃ H : ZFSet.{0}, SubZ H L ∧ ZFSet.card H = β ∧ Hom1Z c H)

theorem card_preimage {L H : ZFSet.{0}} (hHL : SubZ H L) {V : Type} (e : V ≃ L) :
    #{v : V | (e v).1 ∈ H} = ZFSet.card H := by
  apply Cardinal.lift_injective.{1}
  have : Cardinal.lift.{1} #{v : V | (e v).1 ∈ H} = Cardinal.lift.{0} #H := by
    refine Cardinal.lift_mk_eq'.2 ⟨{
      toFun := fun v => ⟨(e v.1).1, v.2⟩
      invFun := fun h => ⟨e.symm ⟨h.1, hHL h.1 h.2⟩, by
        show (e (e.symm _)).1 ∈ H
        rw [Equiv.apply_symm_apply]; exact h.2⟩
      left_inv := fun v => by
        apply Subtype.ext
        show e.symm _ = v.1
        rw [Equiv.symm_apply_eq]
      right_inv := fun h => by
        apply Subtype.ext
        show (e (e.symm _)).1 = h.1
        rw [Equiv.apply_symm_apply] }⟩
  rw [this, Cardinal.lift_uzero, ZFSet.cardinalMk_coe_sort]

theorem one_ne_empty : ({∅} : ZFSet.{0}) ≠ ∅ := by
  intro h
  have : (∅ : ZFSet.{0}) ∈ ({∅} : ZFSet.{0}) := ZFSet.mem_singleton.2 rfl
  rw [h] at this
  exact ZFSet.notMem_empty _ this

theorem oneZ_iff (i : ZFSet.{0}) : OneZ i ↔ i = {∅} := by
  constructor
  · intro h
    ext z
    rw [h z, ZFSet.mem_singleton]
  · rintro rfl z
    exact ZFSet.mem_singleton

/-- Set-theoretic partition relation ⇒ Mathlib's `PairArrow` (needs ordinal elements). -/
theorem pairArrow_of_semArrow {L : ZFSet.{0}} (hL : ∀ x ∈ L, ZFSet.IsOrdinal x)
    {α β : Cardinal.{0}} (h : SemArrow L α β) : Erdos1220.PairArrow (ZFSet.card L) α β := by
  classical
  intro V hV color
  obtain ⟨e⟩ : Nonempty (V ≃ L) := by
    apply Cardinal.lift_mk_eq'.1
    rw [hV, ZFSet.cardinalMk_coe_sort, Cardinal.lift_uzero]
  let col2 : V → V → Bool := fun a b =>
    if hab : a ≠ b then color ⟨{a, b}, Finset.card_pair hab⟩ else false
  let iv : V → V → ZFSet.{0} := fun a b => if col2 a b then {∅} else ∅
  let c : ZFSet.{0} := ZFSet.range (fun p : {p : V × V // (e p.1).1 ∈ (e p.2).1} =>
    ZFSet.pair (ZFSet.pair (e p.1.1).1 (e p.1.2).1) (iv p.1.1 p.1.2))
  have hmem : ∀ a b : V, (e a).1 ∈ (e b).1 →
      ZFSet.pair (ZFSet.pair (e a).1 (e b).1) (iv a b) ∈ c := by
    intro a b hab
    exact ZFSet.mem_range.2 ⟨⟨(a, b), hab⟩, rfl⟩
  have huniq : ∀ a b : V, ∀ i : ZFSet.{0},
      ZFSet.pair (ZFSet.pair (e a).1 (e b).1) i ∈ c → i = iv a b := by
    intro a b i hi
    obtain ⟨⟨⟨a', b'⟩, _⟩, hp⟩ := ZFSet.mem_range.1 hi
    have hp' := ZFSet.pair_inj.1 hp
    have hp1 := ZFSet.pair_inj.1 hp'.1
    have ha' : a' = a := e.injective (Subtype.ext hp1.1)
    have hb' : b' = b := e.injective (Subtype.ext hp1.2)
    have hiv : iv a' b' = i := hp'.2
    rw [← ha', ← hb']
    exact hiv.symm
  have hcol : ColZ L c := by
    intro x hx y hy hxy
    refine ⟨iv (e.symm ⟨x, hx⟩) (e.symm ⟨y, hy⟩), ?_, ?_, ?_⟩
    · have := hmem (e.symm ⟨x, hx⟩) (e.symm ⟨y, hy⟩) (by simpa using hxy)
      simpa using this
    · by_cases hc : col2 (e.symm ⟨x, hx⟩) (e.symm ⟨y, hy⟩)
      · right
        rw [oneZ_iff]
        simp only [iv, hc, if_true]
      · left
        simp only [iv, hc]
        rfl
    · intro i' hi'
      apply huniq
      simpa using hi'
  have hcol2_pair : ∀ a b : V, (hab : a ≠ b) → col2 a b = color ⟨{a, b}, Finset.card_pair hab⟩ := by
    intro a b hab
    simp only [col2, dif_pos hab]
  have hsymm : ∀ a b : V, (hab : a ≠ b) →
      color ⟨{a, b}, Finset.card_pair hab⟩ = color ⟨{b, a}, Finset.card_pair hab.symm⟩ := by
    intro a b hab
    congr 1
    exact Subtype.ext (Finset.pair_comm a b)
  -- the key: for `x ≠ y` in `H`, reduce to the ordered case
  have hord : ∀ a b : V, a ≠ b → (e a).1 ∈ (e b).1 ∨ (e b).1 ∈ (e a).1 := by
    intro a b hab
    rcases ZFSet.IsOrdinal.mem_trichotomous (hL _ (e a).2) (hL _ (e b).2) with h | h | h
    · exact Or.inl h
    · exact absurd (e.injective (Subtype.ext h)) hab
    · exact Or.inr h
  rcases h c hcol with ⟨H, hHL, hcard, hhom⟩ | ⟨H, hHL, hcard, hhom⟩
  · left
    refine ⟨{v : V | (e v).1 ∈ H}, by rw [card_preimage hHL e, hcard], ?_⟩
    intro s hs hsH
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hs
    have ha : (e a).1 ∈ H := hsH (by simp)
    have hb : (e b).1 ∈ H := hsH (by simp)
    have key : ∀ a b : V, (hab : a ≠ b) → (e a).1 ∈ H → (e b).1 ∈ H → (e a).1 ∈ (e b).1 →
        color ⟨{a, b}, Finset.card_pair hab⟩ = false := by
      intro a b hab ha hb h
      have h0 := hhom _ ha _ hb h (iv a b) (hmem a b h)
      rw [← hcol2_pair a b hab]
      by_contra hc
      simp only [iv, Bool.not_eq_false] at h0 hc
      rw [if_pos hc] at h0
      exact one_ne_empty h0
    rcases hord a b hab with h | h
    · exact key a b hab ha hb h
    · rw [hsymm a b hab]; exact key b a hab.symm hb ha h
  · right
    refine ⟨{v : V | (e v).1 ∈ H}, by rw [card_preimage hHL e, hcard], ?_⟩
    intro s hs hsH
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hs
    have ha : (e a).1 ∈ H := hsH (by simp)
    have hb : (e b).1 ∈ H := hsH (by simp)
    have key : ∀ a b : V, (hab : a ≠ b) → (e a).1 ∈ H → (e b).1 ∈ H → (e a).1 ∈ (e b).1 →
        color ⟨{a, b}, Finset.card_pair hab⟩ = true := by
      intro a b hab ha hb h
      have h1 := (oneZ_iff _).1 (hhom _ ha _ hb h (iv a b) (hmem a b h))
      rw [← hcol2_pair a b hab]
      by_contra hc
      simp only [iv, Bool.not_eq_true] at h1 hc
      rw [hc] at h1
      exact one_ne_empty (by simpa using h1.symm)
    rcases hord a b hab with h | h
    · exact key a b hab ha hb h
    · rw [hsymm a b hab]; exact key b a hab.symm hb ha h

/-- Mathlib's `PairArrow` ⇒ the set-theoretic partition relation. -/
theorem semArrow_of_pairArrow {L : ZFSet.{0}} {α β : Cardinal.{0}}
    (h : Erdos1220.PairArrow (ZFSet.card L) α β) : SemArrow L α β := by
  classical
  intro c hcol
  let V := Shrink.{0} L
  let e : V ≃ L := (equivShrink L).symm
  have hV : #V = ZFSet.card L := rfl
  let color : {s : Finset V // s.card = 2} → Bool := fun s =>
    decide (∃ a ∈ s.1, ∃ b ∈ s.1, (e a).1 ∈ (e b).1 ∧
      ZFSet.pair (ZFSet.pair (e a).1 (e b).1) {∅} ∈ c)
  -- the image of a set of `V` in `L`
  have himage : ∀ H : Set V, ∃ HZ : ZFSet.{0}, SubZ HZ L ∧ ZFSet.card HZ = #H ∧
      ∀ v : V, (e v).1 ∈ HZ ↔ v ∈ H := by
    intro H
    refine ⟨ZFSet.sep (fun z => ∃ v ∈ H, (e v).1 = z) L, fun z hz => (ZFSet.mem_sep.1 hz).1,
      ?_, ?_⟩
    · have hset : {v : V | (e v).1 ∈ ZFSet.sep (fun z => ∃ v ∈ H, (e v).1 = z) L} = H := by
        ext v
        simp only [Set.mem_setOf_eq, ZFSet.mem_sep]
        constructor
        · rintro ⟨-, w, hw, hwv⟩
          have : w = v := e.injective (Subtype.ext hwv)
          exact this ▸ hw
        · intro hv
          exact ⟨(e v).2, v, hv, rfl⟩
      rw [← card_preimage (fun z hz => (ZFSet.mem_sep.1 hz).1) e, hset]
    · intro v
      simp only [ZFSet.mem_sep]
      constructor
      · rintro ⟨-, w, hw, hwv⟩
        have : w = v := e.injective (Subtype.ext hwv)
        exact this ▸ hw
      · intro hv
        exact ⟨(e v).2, v, hv, rfl⟩
  -- values of the colouring
  have hval : ∀ x y : ZFSet.{0}, x ∈ L → y ∈ L → x ∈ y → ∀ i : ZFSet.{0},
      ZFSet.pair (ZFSet.pair x y) i ∈ c →
        (ZFSet.pair (ZFSet.pair x y) {∅} ∈ c → i = {∅}) ∧
        (ZFSet.pair (ZFSet.pair x y) {∅} ∉ c → i = ∅) := by
    intro x y hx hy hxy i hi
    obtain ⟨i₀, hi₀, h01, hu⟩ := hcol x hx y hy hxy
    have hii : i = i₀ := hu i hi
    refine ⟨fun h1 => hii.trans (hu _ h1).symm, fun h1 => ?_⟩
    rcases h01 with h0 | h0
    · exact hii.trans h0
    · rw [oneZ_iff] at h0
      exact absurd (h0 ▸ hi₀) h1
  rcases h V hV color with ⟨H, hcard, hhom⟩ | ⟨H, hcard, hhom⟩
  · left
    obtain ⟨HZ, hsub, hcardZ, hmemZ⟩ := himage H
    refine ⟨HZ, hsub, hcardZ.trans hcard, ?_⟩
    intro x hx y hy hxy i hi
    obtain ⟨a, rfl⟩ : ∃ a : V, (e a).1 = x := ⟨e.symm ⟨x, hsub x hx⟩, by simp⟩
    obtain ⟨b, rfl⟩ : ∃ b : V, (e b).1 = y := ⟨e.symm ⟨y, hsub y hy⟩, by simp⟩
    have hab : a ≠ b := by
      rintro rfl; exact ZFSet.mem_irrefl _ hxy
    have hc := hhom {a, b} (Finset.card_pair hab)
      (by
        intro v hv
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact (hmemZ _).1 hx
        · exact (hmemZ _).1 hy)
    refine (hval _ _ (e a).2 (e b).2 hxy i hi).2 fun hmem => ?_
    simp only [color, decide_eq_false_iff_not] at hc
    exact hc ⟨a, by simp, b, by simp, hxy, hmem⟩
  · right
    obtain ⟨HZ, hsub, hcardZ, hmemZ⟩ := himage H
    refine ⟨HZ, hsub, hcardZ.trans hcard, ?_⟩
    intro x hx y hy hxy i hi
    obtain ⟨a, rfl⟩ : ∃ a : V, (e a).1 = x := ⟨e.symm ⟨x, hsub x hx⟩, by simp⟩
    obtain ⟨b, rfl⟩ : ∃ b : V, (e b).1 = y := ⟨e.symm ⟨y, hsub y hy⟩, by simp⟩
    have hab : a ≠ b := by
      rintro rfl; exact ZFSet.mem_irrefl _ hxy
    have hc := hhom {a, b} (Finset.card_pair hab)
      (by
        intro v hv
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact (hmemZ _).1 hx
        · exact (hmemZ _).1 hy)
    simp only [color, decide_eq_true_eq] at hc
    obtain ⟨a', ha', b', hb', hab', hmem⟩ := hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
    rw [oneZ_iff]
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd hab' (ZFSet.mem_irrefl _)
    · exact (hval _ _ (e a').2 (e b').2 hxy i hi).1 hmem
    · exact absurd hab' (ZFSet.mem_asymm hxy)
    · exact absurd hab' (ZFSet.mem_irrefl _)

theorem semArrow_iff {L : ZFSet.{0}} (hL : ∀ x ∈ L, ZFSet.IsOrdinal x) (α β : Cardinal.{0}) :
    SemArrow L α β ↔ Erdos1220.PairArrow (ZFSet.card L) α β :=
  ⟨pairArrow_of_semArrow hL, semArrow_of_pairArrow⟩

end Erdos1220.FOL

#print axioms Erdos1220.FOL.semArrow_iff
