/-
# Erdős #1220 — faithfulness of the sentence `Erdos1220`

`erdos1220_sentence_faithful : (ZFSet.{0} ⊨ Erdos1220) ↔ Erdos1220.Problem1220.{0}`:
in Mathlib's `ZFSet` with erdos501's standard interpretation of `∅, ω, 𝒫, ⋃, (·,·), ∈`, the
first-order sentence holds iff the Mathlib-level statement of problem #1220 holds.
-/
import Erdos1220Full.Cof1220
import Erdos1220Full.Arrow1220

open Cardinal
open scoped FirstOrder
open FirstOrder FirstOrder.Language

namespace Erdos1220.FOL

theorem isOrdinal_of_mem_cz {κ : Cardinal.{0}} : ∀ x ∈ cz κ, ZFSet.IsOrdinal x :=
  fun _ hx => (ZFSet.isOrdinal_toZFSet _).mem hx

theorem conclusion_iff (κ : Cardinal.{0}) (c : ZFSet.{0}) :
    ((∃ H : ZFSet.{0}, SubZ H (cz κ) ∧ (LeqZ H (cz κ) ∧ LeqZ (cz κ) H) ∧ Hom0Z c H) ∨
      (∃ w : ZFSet.{0}, Om1Z w ∧
        ∃ H : ZFSet.{0}, SubZ H (cz κ) ∧ (LeqZ H w ∧ LeqZ w H) ∧ Hom1Z c H)) ↔
    ((∃ H : ZFSet.{0}, SubZ H (cz κ) ∧ ZFSet.card H = κ ∧ Hom0Z c H) ∨
      (∃ H : ZFSet.{0}, SubZ H (cz κ) ∧ ZFSet.card H = ℵ₁ ∧ Hom1Z c H)) := by
  apply or_congr
  · refine exists_congr fun H => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [leqZ_iff, leqZ_iff, card_cz, ← le_antisymm_iff]
  · constructor
    · rintro ⟨w, hw, H, hH, ⟨h1, h2⟩, hhom⟩
      rw [leqZ_iff] at h1 h2
      rw [card_of_om1Z hw] at h1 h2
      exact ⟨H, hH, le_antisymm h1 h2, hhom⟩
    · rintro ⟨H, hH, hcard, hhom⟩
      refine ⟨cz ℵ₁, om1Z_cz, H, hH, ?_, hhom⟩
      rw [leqZ_iff, leqZ_iff, card_cz, hcard]
      exact ⟨le_rfl, le_rfl⟩

theorem arrow_cz_iff (κ : Cardinal.{0}) :
    (∀ c : ZFSet.{0}, ColZ (cz κ) c →
      (∃ H : ZFSet.{0}, SubZ H (cz κ) ∧ (LeqZ H (cz κ) ∧ LeqZ (cz κ) H) ∧ Hom0Z c H) ∨
      (∃ w : ZFSet.{0}, Om1Z w ∧
        ∃ H : ZFSet.{0}, SubZ H (cz κ) ∧ (LeqZ H w ∧ LeqZ w H) ∧ Hom1Z c H)) ↔
    Erdos1220.PairArrow κ κ ℵ₁ := by
  have h := semArrow_iff (isOrdinal_of_mem_cz (κ := κ)) κ ℵ₁
  rw [card_cz] at h
  rw [← h, SemArrow]
  exact forall_congr' fun c => imp_congr_right fun _ => conclusion_iff κ c

/-- **The set-theoretic content of `Erdos1220` is `Problem1220`.** -/
theorem semZ_iff : SemZ ↔ Erdos1220.Problem1220.{0} := by
  unfold SemZ Erdos1220.Problem1220 Erdos1220.Hypotheses
  constructor
  · rintro h κ ⟨hs, ho, hcof⟩
    exact (arrow_cz_iff κ).1 (h (cz κ) ⟨(cardZ_iff _).2 ⟨κ, rfl⟩, (singZ_cz_iff κ).2 hs,
      (oInaccZ_cz_iff κ).2 ho, (cof_oInaccZ_iff κ).2 hcof⟩)
  · rintro h l ⟨hc, hs, ho, hcof⟩
    obtain ⟨κ, rfl⟩ := (cardZ_iff l).1 hc
    exact (arrow_cz_iff κ).2 (h κ ⟨(singZ_cz_iff κ).1 hs, (oInaccZ_cz_iff κ).1 ho,
      (cof_oInaccZ_iff κ).1 hcof⟩)

/-- **Faithfulness of the rendering** (target 2): in Mathlib's `ZFSet` (erdos501's standard
interpretation `zfsetStructure`), the sentence `Erdos1220` holds iff the Mathlib-level statement
`Erdos1220.Problem1220` (universe `0`) holds. -/
theorem erdos1220_sentence_faithful :
    (ZFSet.{0} ⊨ Erdos1220.FOL.Erdos1220) ↔ Erdos1220.Problem1220.{0} :=
  realize_Erdos1220_iff_SemZ.trans semZ_iff

theorem erdos1220SentenceFaithful : Erdos1220SentenceFaithful :=
  erdos1220_sentence_faithful

end Erdos1220.FOL

#print axioms Erdos1220.FOL.erdos1220_sentence_faithful
#print axioms Erdos1220.FOL.erdos1220SentenceFaithful
