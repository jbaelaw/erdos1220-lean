/-
Transfinite generalization of Flypitch4/Erdos501/OmegaClosed.lean
(`exists_forall_of_denseOmegaClosed`). Copyright of the original: The Flypitch
Project, Apache 2.0 (see NOTICE).
-/
import Flypitch4.ForcingCH

/-!
# Distributivity from a pure-extension strategy

Shelah–Stanley §3.8: the historical forcing is `μ⁺`-strategically closed.
Player II answers every move by a *pure* extension, and pure chains of
length at most `θ` have pure upper bounds. Abstractly, inside a complete
Boolean algebra we record:

* a dense set `D` of nonzero elements (images of conditions);
* a relation `R d d'` ("`d'` purely extends `d`"), transitive, with `d' ≤ d`;
* every nonzero `b ≤ d ∈ D` contains a pure extension `d' ∈ D` of `d`;
* every nonempty `R`-chain of length at most `θ` in `D` has an `R`-bound in `D`.

From this, `θ` many choices can be made simultaneously below any nonzero `Γ`
(`exists_forall_of_pureClosure`). This is the form of
`(θ, ∞)`-distributivity used to show that no new short sequences are added.
-/

open Flypitch

namespace Erdos1220Full

universe u v

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- An abstract pure-extension strategy with chain bounds up to length `θ`. -/
structure PureClosure (D : Set 𝔹) (R : 𝔹 → 𝔹 → Prop) (θ : Ordinal.{v}) : Prop where
  pos : ∀ d ∈ D, ⊥ < d
  dense : ∀ b : 𝔹, ⊥ < b → ∃ d ∈ D, d ≤ b
  refine : ∀ d ∈ D, ∀ b : 𝔹, ⊥ < b → b ≤ d → ∃ d' ∈ D, d' ≤ b ∧ R d d'
  R_le : ∀ {d d' : 𝔹}, R d d' → d' ≤ d
  R_trans : ∀ {a b c : 𝔹}, R a b → R b c → R a c
  bound : ∀ α : Ordinal.{v}, α ≤ θ → 0 < α → ∀ s : Ordinal.{v} → 𝔹,
    (∀ β < α, s β ∈ D) → (∀ β γ, β < γ → γ < α → R (s β) (s γ)) →
    ∃ d ∈ D, ∀ β < α, R (s β) d

namespace PureClosure

variable {D : Set 𝔹} {R : 𝔹 → 𝔹 → Prop} {θ : Ordinal.{v}}
variable (hP : PureClosure D R θ) {Γ : 𝔹} (hΓ : ⊥ < Γ)
variable {ι : Ordinal.{v} → Type*} (φ : ∀ α, ι α → 𝔹)

/-- The next move exists at stage `α` above the position `p`. -/
def NextE (p : 𝔹) (α : Ordinal.{v}) : Prop :=
  ∃ q : ι α × 𝔹, q.2 ∈ D ∧ q.2 ≤ p ⊓ φ α q.1 ∧ R p q.2

open Classical in
/-- The starting point below `Γ`. -/
noncomputable def start : 𝔹 := Classical.choose (hP.dense Γ hΓ)

theorem start_spec : hP.start hΓ ∈ D ∧ hP.start hΓ ≤ Γ :=
  Classical.choose_spec (hP.dense Γ hΓ)

open Classical in
/-- The position before stage `α`, computed from the earlier moves `f`. -/
noncomputable def prev (f : Ordinal.{v} → 𝔹) (α : Ordinal.{v}) : 𝔹 :=
  if α = 0 then hP.start hΓ
  else if h : ∃ d ∈ D, ∀ β < α, R (f β) d then Classical.choose h else hP.start hΓ

open Classical in
/-- The move at stage `α`. -/
noncomputable def move (f : Ordinal.{v} → 𝔹) (α : Ordinal.{v}) : 𝔹 :=
  if h : NextE (D := D) (R := R) φ (hP.prev hΓ f α) α then (Classical.choose h).2 else ⊥

/-- The whole run, by well-founded recursion on ordinals. -/
noncomputable def run : Ordinal.{v} → 𝔹 :=
  Ordinal.lt_wf.fix fun α IH =>
    open Classical in hP.move hΓ φ (fun β => if h : β < α then IH β h else ⊥) α

theorem run_eq (α : Ordinal.{v}) :
    hP.run hΓ φ α = hP.move hΓ φ (fun β => if β < α then hP.run hΓ φ β else ⊥) α := by
  classical
  unfold run
  rw [WellFoundedLT.fix_eq]
  congr 1

/-- Restriction of the run below `α`. -/
noncomputable def below (α : Ordinal.{v}) : Ordinal.{v} → 𝔹 :=
  fun β => if β < α then hP.run hΓ φ β else ⊥

theorem run_eq' (α : Ordinal.{v}) :
    hP.run hΓ φ α = hP.move hΓ φ (hP.below hΓ φ α) α :=
  hP.run_eq hΓ φ α

/-- The invariant maintained at stage `α`. -/
def Good (α : Ordinal.{v}) : Prop :=
  hP.run hΓ φ α ∈ D ∧ hP.run hΓ φ α ≤ Γ ∧
    NextE (D := D) (R := R) φ (hP.prev hΓ (hP.below hΓ φ α) α) α ∧
    ∀ β < α, R (hP.run hΓ φ β) (hP.run hΓ φ α)

variable {φ}
variable (hφ : ∀ α < θ, ∀ Γ' : 𝔹, ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ α i)

include hφ in
theorem good (α : Ordinal.{v}) (hα : α < θ) : hP.Good hΓ φ α := by
  classical
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  -- the position before `α`
  set p := hP.prev hΓ (hP.below hΓ φ α) α with hp
  have hpos : p ∈ D ∧ p ≤ Γ ∧ ∀ β < α, R (hP.run hΓ φ β) p := by
    by_cases h0 : α = 0
    · have : p = hP.start hΓ := by simp only [hp, prev, h0, if_true]
      rw [this]
      exact ⟨(hP.start_spec hΓ).1, (hP.start_spec hΓ).2, fun β hβ => by
        rw [h0] at hβ; exact absurd hβ (by simp)⟩
    · have hα0 : 0 < α := pos_iff_ne_zero.mpr h0
      have hex : ∃ d ∈ D, ∀ β < α, R (hP.below hΓ φ α β) d := by
        apply hP.bound α (hα.le) hα0
        · intro β hβ
          simp only [below, if_pos hβ]
          exact (IH β hβ (hβ.trans hα)).1
        · intro β γ hβγ hγ
          simp only [below, if_pos hγ, if_pos (hβγ.trans hγ)]
          exact (IH γ hγ (hγ.trans hα)).2.2.2 β hβγ
      have hpeq : p = Classical.choose hex := by
        simp only [hp, prev, h0, if_false, dif_pos hex]
      have hspec := Classical.choose_spec hex
      rw [← hpeq] at hspec
      have hR : ∀ β < α, R (hP.run hΓ φ β) p := by
        intro β hβ
        have := hspec.2 β hβ
        simpa only [below, if_pos hβ] using this
      refine ⟨hspec.1, ?_, hR⟩
      exact (hP.R_le (hR 0 hα0)).trans (IH 0 hα0 (hα0.trans hα)).2.1
  obtain ⟨hpD, hpΓ, hpR⟩ := hpos
  -- the next move exists
  have hnext : NextE (D := D) (R := R) φ p α := by
    obtain ⟨i, hi⟩ := hφ α hα p (hP.pos p hpD) hpΓ
    obtain ⟨d', hd'D, hd'le, hR⟩ := hP.refine p hpD (p ⊓ φ α i) hi inf_le_left
    exact ⟨(i, d'), hd'D, hd'le, hR⟩
  have hrun : hP.run hΓ φ α = (Classical.choose hnext).2 := by
    rw [run_eq', move, dif_pos hnext]
  have hspec := Classical.choose_spec hnext
  refine ⟨?_, ?_, hnext, ?_⟩
  · rw [hrun]; exact hspec.1
  · rw [hrun]; exact hspec.2.1.trans (inf_le_left.trans hpΓ)
  · intro β hβ
    rw [hrun]
    exact hP.R_trans (hpR β hβ) hspec.2.2

include hP hΓ hφ in
/-- **Distributivity.** `θ` many choices can be made simultaneously below `Γ`. -/
theorem exists_forall :
    ∃ Γ' : 𝔹, ⊥ < Γ' ∧ Γ' ≤ Γ ∧ ∃ c : ∀ α, α < θ → ι α, ∀ α (hα : α < θ), Γ' ≤ φ α (c α hα) := by
  classical
  have hG := fun α (hα : α < θ) => hP.good hΓ hφ α hα
  let c : ∀ α, α < θ → ι α := fun α hα => (Classical.choose (hG α hα).2.2.1).1
  have hc : ∀ α (hα : α < θ), hP.run hΓ φ α ≤ φ α (c α hα) := by
    intro α hα
    have hnext := (hG α hα).2.2.1
    have hspec := Classical.choose_spec hnext
    have hrun : hP.run hΓ φ α = (Classical.choose hnext).2 := by
      rw [run_eq', move, dif_pos hnext]
    rw [hrun]
    exact hspec.2.1.trans inf_le_right
  by_cases hθ : θ = 0
  · refine ⟨hP.start hΓ, hP.pos _ (hP.start_spec hΓ).1, (hP.start_spec hΓ).2, c, ?_⟩
    intro α hα
    rw [hθ] at hα
    exact absurd hα (by simp)
  · have hθ0 : 0 < θ := pos_iff_ne_zero.mpr hθ
    obtain ⟨d, hdD, hdR⟩ := hP.bound θ le_rfl hθ0 (hP.run hΓ φ)
      (fun β hβ => (hG β hβ).1) (fun β γ hβγ hγ => (hG γ hγ).2.2.2 β hβγ)
    refine ⟨d, hP.pos d hdD, (hP.R_le (hdR 0 hθ0)).trans (hG 0 hθ0).2.1, c, ?_⟩
    intro α hα
    exact (hP.R_le (hdR α hα)).trans (hc α hα)

include hP hΓ in
/-- Witness form: choosing, for `θ` many suprema, a term of each on one piece. -/
theorem exists_witness (h : ∀ α < θ, Γ ≤ ⨆ i, φ α i) :
    ∃ Γ' : 𝔹, ⊥ < Γ' ∧ Γ' ≤ Γ ∧ ∃ c : ∀ α, α < θ → ι α, ∀ α (hα : α < θ), Γ' ≤ φ α (c α hα) := by
  exact exists_forall hP hΓ (φ := φ) fun α hα Γ' hΓ' hle =>
    nonzero_inf_of_nonzero_le_supr hΓ' (hle.trans (h α hα))

end PureClosure
end Erdos1220Full

#print axioms Erdos1220Full.PureClosure.exists_forall
#print axioms Erdos1220Full.PureClosure.exists_witness
