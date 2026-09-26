/-
# Erdős #1220 — cofinality, singularity, `ℵ₀`-inaccessibility and `ω₁` in `ZFSet.{0}`
-/
import Erdos1220Full.Card1220

open Cardinal

namespace Erdos1220.FOL

/-! ### Cofinal subsets of a von Neumann ordinal -/

theorem cof_le_card_of_cofinal {o : Ordinal.{0}} {S : ZFSet.{0}} (hS : SubZ S o.toZFSet)
    (hc : CofinalZ S o.toZFSet) : o.cof ≤ ZFSet.card S := by
  let s : Set (Set.Iio o) := {a | a.1.toZFSet ∈ S}
  have hcof : IsCofinal s := by
    intro a
    obtain ⟨g, hgS, hag⟩ := hc a.1.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.2 a.2)
    obtain ⟨b, hb, rfl⟩ := Ordinal.mem_toZFSet_iff.1 (hS g hgS)
    refine ⟨⟨b, hb⟩, hgS, ?_⟩
    show a.1 ≤ b
    rcases hag with h | h
    · exact (Ordinal.toZFSet_mem_toZFSet_iff.1 h).le
    · exact (Ordinal.toZFSet_injective h).le
  have h1 : Order.cof (Set.Iio o) ≤ #s := Order.cof_le hcof
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof] at h1
  have h2 : #s ≤ #S := by
    refine Cardinal.mk_le_of_injective (f := fun x : s => (⟨x.1.1.toZFSet, x.2⟩ : S)) ?_
    intro x y hxy
    have := Ordinal.toZFSet_injective (congrArg Subtype.val hxy)
    exact Subtype.ext (Subtype.ext this)
  rw [ZFSet.cardinalMk_coe_sort] at h2
  exact Cardinal.lift_le.1 (h1.trans h2)

theorem exists_cofinal_card_eq (o : Ordinal.{0}) :
    ∃ S : ZFSet.{0}, SubZ S o.toZFSet ∧ CofinalZ S o.toZFSet ∧ ZFSet.card S = o.cof := by
  obtain ⟨s, hs, hcard⟩ := Order.exists_cof_eq (Set.Iio o)
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof] at hcard
  let S : ZFSet.{0} := ZFSet.sep (fun z => ∃ a ∈ s, a.1.toZFSet = z) o.toZFSet
  refine ⟨S, fun z hz => (ZFSet.mem_sep.1 hz).1, fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.1 hb
    obtain ⟨c, hcs, hac⟩ := hs ⟨a, ha⟩
    refine ⟨c.1.toZFSet, ZFSet.mem_sep.2 ⟨Ordinal.toZFSet_mem_toZFSet_iff.2 c.2, c, hcs, rfl⟩, ?_⟩
    have hac' : a ≤ c.1 := hac
    rcases hac'.lt_or_eq with h | h
    · exact Or.inl (Ordinal.toZFSet_mem_toZFSet_iff.2 h)
    · exact Or.inr (congrArg Ordinal.toZFSet h)
  · apply Cardinal.lift_injective.{1}
    rw [← ZFSet.cardinalMk_coe_sort, ← hcard]
    symm
    refine Cardinal.mk_congr (Equiv.ofBijective (fun x : s =>
      (⟨x.1.1.toZFSet, ZFSet.mem_sep.2 ⟨Ordinal.toZFSet_mem_toZFSet_iff.2 x.1.2, x.1, x.2, rfl⟩⟩ : S))
      ⟨?_, ?_⟩)
    · intro x y hxy
      have := Ordinal.toZFSet_injective (congrArg Subtype.val hxy)
      exact Subtype.ext (Subtype.ext this)
    · rintro ⟨z, hz⟩
      obtain ⟨-, a, ha, rfl⟩ := ZFSet.mem_sep.1 hz
      exact ⟨⟨a, ha⟩, rfl⟩

/-! ### Singular cardinals -/

theorem leqZ_omega_cz (κ : Cardinal.{0}) : LeqZ ZFSet.omega (cz κ) ↔ ℵ₀ ≤ κ := by
  rw [leqZ_iff, card_omega, card_cz]

theorem singZ_cz_iff (κ : Cardinal.{0}) : SingZ (cz κ) ↔ κ.IsSingular := by
  unfold SingZ
  rw [leqZ_omega_cz]
  have key : (∃ S : ZFSet.{0}, SubZ S (cz κ) ∧ CofinalZ S (cz κ) ∧ ¬ LeqZ (cz κ) S) ↔
      κ.ord.cof < κ := by
    constructor
    · rintro ⟨S, hS, hc, hlt⟩
      rw [leqZ_iff, card_cz, not_le] at hlt
      exact (cof_le_card_of_cofinal hS hc).trans_lt hlt
    · intro h
      obtain ⟨S, hS, hc, hcard⟩ := exists_cofinal_card_eq κ.ord
      refine ⟨S, hS, hc, ?_⟩
      rw [leqZ_iff, card_cz, hcard, not_le]
      exact h
  rw [key]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.ne⟩, fun h => ⟨h.aleph0_le, h.cof_ord_lt⟩⟩

/-! ### The cofinality as a von Neumann cardinal -/

theorem cofZ_cz_iff (κ : Cardinal.{0}) (d : ZFSet.{0}) : CofZ (cz κ) d ↔ d = cz κ.ord.cof := by
  constructor
  · rintro ⟨hd, ⟨S, hS, hc, hle1, hle2⟩, hall⟩
    obtain ⟨μ, rfl⟩ := (cardZ_iff d).1 hd
    congr 1
    rw [leqZ_iff, card_cz] at hle1 hle2
    obtain ⟨S₁, hS₁, hc₁, hcard₁⟩ := exists_cofinal_card_eq κ.ord
    have h3 := hall S₁ hS₁ hc₁
    rw [leqZ_iff, card_cz, hcard₁] at h3
    exact le_antisymm h3 ((cof_le_card_of_cofinal hS hc).trans hle1)
  · rintro rfl
    refine ⟨(cardZ_iff _).2 ⟨_, rfl⟩, ?_, fun S hS hc => ?_⟩
    · obtain ⟨S, hS, hc, hcard⟩ := exists_cofinal_card_eq κ.ord
      refine ⟨S, hS, hc, ?_, ?_⟩
      · rw [leqZ_iff, card_cz, hcard]
      · rw [leqZ_iff, card_cz, hcard]
    · rw [leqZ_iff, card_cz]
      exact cof_le_card_of_cofinal hS hc

theorem cof_oInaccZ_iff (κ : Cardinal.{0}) :
    (∀ d : ZFSet.{0}, CofZ (cz κ) d → OInaccZ d) ↔ Erdos1220.IsOmegaInaccessible κ.ord.cof := by
  constructor
  · intro h
    exact (oInaccZ_cz_iff _).1 (h _ ((cofZ_cz_iff κ _).2 rfl))
  · intro h d hd
    rw [(cofZ_cz_iff κ d).1 hd]
    exact (oInaccZ_cz_iff _).2 h

/-! ### `ω₁` -/

theorem card_of_om1Z {w : ZFSet.{0}} (hw : Om1Z w) : ZFSet.card w = ℵ₁ := by
  obtain ⟨hord, hnle, hall⟩ := hw
  rw [ordZ_iff] at hord
  obtain ⟨o, rfl⟩ : ∃ o : Ordinal.{0}, o.toZFSet = w := ⟨_, hord.toZFSet_rank_eq⟩
  rw [leqZ_iff, card_omega, Ordinal.card_toZFSet, not_le] at hnle
  rw [Ordinal.card_toZFSet]
  have hge : ℵ₁ ≤ o.card := by
    rw [← Cardinal.succ_aleph0]; exact Order.succ_le_of_lt hnle
  refine le_antisymm ?_ hge
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : (ℵ₁ : Cardinal.{0}).ord < o := by
    by_contra hc
    rw [not_lt] at hc
    have := Ordinal.card_le_card hc
    rw [Cardinal.card_ord] at this
    exact absurd hlt (not_lt.2 this)
  have := hall _ (Ordinal.toZFSet_mem_toZFSet_iff.2 hlt')
  rw [leqZ_iff, card_omega, Ordinal.card_toZFSet, Cardinal.card_ord] at this
  exact absurd this (not_le.2 Cardinal.aleph0_lt_aleph_one)

theorem om1Z_cz : Om1Z (cz ℵ₁) := by
  refine ⟨(ordZ_iff _).2 (ZFSet.isOrdinal_toZFSet _), ?_, fun a ha => ?_⟩
  · rw [leqZ_iff, card_cz, card_omega, not_le]
    exact Cardinal.aleph0_lt_aleph_one
  · obtain ⟨b, hb, rfl⟩ := mem_cz_iff.1 ha
    rw [leqZ_iff, card_omega, card_toZFSet_eq]
    rw [← Cardinal.succ_aleph0] at hb
    exact Order.lt_succ_iff.1 hb

end Erdos1220.FOL

#print axioms Erdos1220.FOL.singZ_cz_iff
#print axioms Erdos1220.FOL.cof_oInaccZ_iff
#print axioms Erdos1220.FOL.card_of_om1Z
