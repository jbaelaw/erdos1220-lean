/-
Portions adapted from `Flypitch4/Erdos501/DeltaSystem.lean` (erdos501 dependency):
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

General Δ-system lemma (ZFC, cardinal form), counting of blueprints, pigeonhole, and the
"chain-condition skeleton" used for the `(2^μ)⁺`-c.c. of the Shelah–Stanley forcing (Sh:258 §3.8).

No GCH: the index cardinal is `θ` with `θ` regular and `∀ ν < θ, ν ^ μ < θ`; the specialization is
`θ = Order.succ (2 ^ μ)`, for which the hypothesis is a ZFC theorem (`(2^μ)^μ = 2^μ`).

The proof of the Δ-system lemma generalizes `Flypitch.Erdos501.delta_system_countable`
(countable sets, `θ = 𝔠⁺`, closure chain of length `ω₁`) to sets of size `≤ μ`, arbitrary
`θ`, and a closure chain of length `μ⁺`.
-/
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.Zorn
import Flypitch4.SetTheoryExt

open Cardinal Set

universe u v

namespace Erdos1220.DeltaSystem

/-! ### Small unions below a regular cardinal -/

lemma mk_iUnion_lt {ι J : Type u} {θ : Cardinal.{u}} (hθ : θ.IsRegular) (f : J → Set ι)
    (hJ : #J < θ) (hf : ∀ j, #(f j) < θ) : #(⋃ j, f j) < θ :=
  (mk_iUnion_le f).trans_lt
    (mul_lt_of_lt hθ.aleph0_le hJ (iSup_lt_of_isRegular hθ hJ hf))

lemma lt_of_pow_hyp {μ θ : Cardinal.{u}} (hθ : θ.IsRegular) (hpow : ∀ ν < θ, ν ^ μ < θ) :
    μ < θ := by
  have h2 : (2 : Cardinal) < θ := by
    exact (ofNat_lt_aleph0 : (2 : Cardinal.{u}) < ℵ₀).trans_le hθ.aleph0_le
  exact (cantor μ).trans (hpow 2 h2)

section Core

variable {A ι : Type u} (S : A → Set ι) {μ θ : Cardinal.{u}}

/-- `F` is *disjoint outside `Y`* if the sets `S a \ Y`, `a ∈ F`, are pairwise disjoint. -/
def DisjOutside (Y : Set ι) (F : Set A) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, a ≠ b → Disjoint (S a \ Y) (S b \ Y)

/-- **Good case**: a family of `≥ θ` indices whose sets are pairwise disjoint outside a set `Y`
of size `< θ` contains a Δ-system of size `θ` (root = common trace on `Y`). -/
lemma exists_delta_of_disjOutside (hμ : ℵ₀ ≤ μ) (hθ : θ.IsRegular)
    (hpow : ∀ ν < θ, ν ^ μ < θ) (hS : ∀ a, #(S a) ≤ μ) (hA : #A = θ)
    {Y : Set ι} (hY : #Y < θ) {F : Set A} (hF : θ ≤ #F) (hdisj : DisjOutside S Y F) :
    ∃ (J : Set A) (R : Set ι), #J = θ ∧ (∀ a ∈ J, R ⊆ S a) ∧
      ∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R := by
  have hμθ : μ < θ := lt_of_pow_hyp hθ hpow
  let tr : F → {t : Set Y // #t ≤ μ} := fun a =>
    ⟨Subtype.val ⁻¹' S a.1,
      (mk_preimage_of_injective Subtype.val (S a.1) Subtype.val_injective).trans (hS a.1)⟩
  have hcount : #{t : Set Y // #t ≤ μ} < θ :=
    (mk_bounded_set_le Y μ).trans_lt (hpow _ (max_lt hY (hμ.trans_lt hμθ)))
  obtain ⟨⟨R', hR'⟩, J, hJF, ⟨hJcard, hJtr⟩⟩ := Cardinal.infinite_pigeonhole_set (s := F) tr
    θ hF hθ.aleph0_le (by rw [hθ.cof_ord]; exact hcount)
  have htr : ∀ a ∈ J, (Subtype.val ⁻¹' S a : Set Y) = R' := fun a ha =>
    congrArg Subtype.val (hJtr ha)
  let R : Set ι := Subtype.val '' R'
  have hR : ∀ a ∈ J, S a ∩ Y = R := by
    intro a ha
    ext x
    constructor
    · rintro ⟨hxa, hxY⟩
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      rw [← htr a ha]
      exact hxa
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (Subtype.val ⁻¹' S a : Set Y) := by rw [htr a ha]; exact hy
      exact ⟨hy', y.2⟩
  refine ⟨J, R, le_antisymm ((Cardinal.mk_set_le J).trans hA.le) hJcard, ?_, ?_⟩
  · intro a ha
    rw [← hR a ha]
    exact inter_subset_left
  · intro a ha b hb hab
    apply subset_antisymm
    · rintro x ⟨hxa, hxb⟩
      by_cases hxY : x ∈ Y
      · rw [← hR a ha]; exact ⟨hxa, hxY⟩
      · exact (Set.disjoint_left.mp (hdisj a (hJF ha) b (hJF hb) hab) ⟨hxa, hxY⟩
          ⟨hxb, hxY⟩).elim
    · intro x hx
      have h1 : x ∈ S a ∩ Y := by rw [hR a ha]; exact hx
      have h2 : x ∈ S b ∩ Y := by rw [hR b hb]; exact hx
      exact ⟨h1.1, h2.1⟩

/-- Families disjoint outside `Y` consisting of sets not contained in `Y`. -/
def Fam (Y : Set ι) : Set (Set A) := {F | (∀ a ∈ F, ¬ S a ⊆ Y) ∧ DisjOutside S Y F}

lemma exists_maximal_fam (Y : Set ι) : ∃ F, Maximal (· ∈ Fam S Y) F := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
  · rintro a ⟨F, hF, haF⟩
    exact (hc hF).1 a haF
  · rintro a ⟨F, hF, haF⟩ b ⟨G, hG, hbG⟩ hab
    rcases hchain.total hF hG with h | h
    · exact (hc hG).2 a (h haF) b hbG hab
    · exact (hc hF).2 a haF b (h hbG) hab

/-- `Y ∪ ⋃_{a ∈ maxFam Y} S a`. -/
def Ynext (maxFam : Set ι → Set A) (Y : Set ι) : Set ι := Y ∪ ⋃ a ∈ maxFam Y, S a

lemma meets_of_maximal {Y : Set ι} {F : Set A} (hmax : Maximal (· ∈ Fam S Y) F) (a : A)
    (ha : ¬ S a ⊆ Y) : (S a ∩ ((Y ∪ ⋃ b ∈ F, S b) \ Y)).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hmem : ∀ x, x ∈ S a → x ∉ Y → x ∉ ⋃ b ∈ F, S b := by
    intro x hxa hxY hx
    have : x ∈ S a ∩ ((Y ∪ ⋃ b ∈ F, S b) \ Y) := ⟨hxa, Or.inr hx, hxY⟩
    rw [hcon] at this
    exact this
  have haF : a ∉ F := by
    intro haF
    obtain ⟨x, hxa, hxY⟩ := Set.not_subset.mp ha
    exact hmem x hxa hxY (mem_biUnion haF hxa)
  have hdisj_a : ∀ b ∈ F, Disjoint (S a \ Y) (S b \ Y) := by
    intro b hb
    rw [Set.disjoint_left]
    rintro x ⟨hxa, hxY⟩ ⟨hxb, -⟩
    exact hmem x hxa hxY (mem_biUnion hb hxb)
  have hins : insert a F ∈ Fam S Y := by
    refine ⟨?_, ?_⟩
    · intro c hc
      rcases mem_insert_iff.mp hc with rfl | hcF
      · exact ha
      · exact hmax.prop.1 c hcF
    · intro c hc d hd hcd
      rcases mem_insert_iff.mp hc with rfl | hcF <;> rcases mem_insert_iff.mp hd with rfl | hdF
      · exact absurd rfl hcd
      · exact hdisj_a d hdF
      · exact (hdisj_a c hcF).symm
      · exact hmax.prop.2 c hcF d hdF hcd
  exact haF (hmax.mem_of_prop_insert hins)

lemma card_Ynext_lt (hθ : θ.IsRegular) (hμθ : μ < θ) (hS : ∀ a, #(S a) ≤ μ)
    {maxFam : Set ι → Set A} {Y : Set ι}
    (hY : #Y < θ) (hF : #(maxFam Y) < θ) : #(Ynext S maxFam Y) < θ := by
  have h1 : #(⋃ a ∈ maxFam Y, S a) < θ :=
    (Cardinal.mk_biUnion_le S (maxFam Y)).trans_lt
      (mul_lt_of_lt hθ.aleph0_le hF ((ciSup_le' fun a : maxFam Y => hS a.1).trans_lt hμθ))
  exact (Cardinal.mk_union_le _ _).trans_lt (add_lt_of_lt hθ.aleph0_le hY h1)

/-! ### The closure chain -/

section chain

variable {W : Type u} [LinearOrder W] [WellFoundedLT W]

noncomputable def chain (maxFam : Set ι → Set A) : W → Set ι :=
  WellFounded.fix wellFounded_lt fun w rec => Ynext S maxFam (⋃ v : Iio w, rec v.1 v.2)

lemma chain_eq (maxFam : Set ι → Set A) (w : W) :
    chain S maxFam w = Ynext S maxFam (⋃ v : Iio w, chain S maxFam v.1) := by
  unfold chain
  rw [WellFounded.fix_eq]

lemma chain_mono (maxFam : Set ι → Set A) {v w : W} (hvw : v ≤ w) :
    chain S maxFam v ⊆ chain S maxFam w := by
  rcases hvw.lt_or_eq with h | rfl
  · rw [chain_eq S maxFam w]
    exact (subset_iUnion (fun v : Iio w => chain S maxFam v.1) ⟨v, h⟩).trans subset_union_left
  · exact subset_refl _

omit [WellFoundedLT W] in
lemma exists_upper_bound_of_small (hμ : ℵ₀ ≤ μ) (hW : ¬ #W ≤ μ) (hIio : ∀ w : W, #(Iio w) ≤ μ)
    {s : Set W} (hs : #s ≤ μ) : ∃ w₀, ∀ w ∈ s, w ≤ w₀ := by
  by_contra h
  apply hW
  have hsub : (univ : Set W) ⊆ ⋃ w ∈ s, Iio w := by
    intro w₀ _
    obtain ⟨w, hw, hlt⟩ : ∃ w ∈ s, ¬ w ≤ w₀ := by
      by_contra h'
      exact h ⟨w₀, fun w hw => by_contra fun hle => h' ⟨w, hw, hle⟩⟩
    exact mem_biUnion hw (not_le.mp hlt)
  rw [← mk_univ]
  calc #(univ : Set W) ≤ #(⋃ w ∈ s, Iio w) := mk_le_mk_of_subset hsub
    _ ≤ #s * ⨆ w : s, #(Iio w.1) := Cardinal.mk_biUnion_le _ _
    _ ≤ μ * μ := mul_le_mul' hs (ciSup_le' fun w => hIio w.1)
    _ = μ := mul_eq_self hμ

omit [WellFoundedLT W] in
lemma exists_gt_of_large (hμ : ℵ₀ ≤ μ) (hW : ¬ #W ≤ μ) (hIio : ∀ w : W, #(Iio w) ≤ μ)
    (w₀ : W) : ∃ w₁, w₀ < w₁ := by
  by_contra h
  apply hW
  have hsub : (univ : Set W) ⊆ insert w₀ (Iio w₀) := by
    intro w _
    rcases (not_lt.mp fun hlt => h ⟨w, hlt⟩).lt_or_eq with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl heq
  rw [← mk_univ]
  calc #(univ : Set W) ≤ #(insert w₀ (Iio w₀) : Set W) := mk_le_mk_of_subset hsub
    _ ≤ #(Iio w₀) + 1 := mk_insert_le
    _ ≤ μ + 1 := add_le_add (hIio w₀) le_rfl
    _ = μ := add_one_eq hμ

variable (hθ : θ.IsRegular) (hμθ : μ < θ) (hS : ∀ a, #(S a) ≤ μ)
  (hIio : ∀ w : W, #(Iio w) ≤ μ)
  {maxFam : Set ι → Set A} (hsmall : ∀ Y : Set ι, #Y < θ → #(maxFam Y) < θ)

include hθ hμθ hS hIio hsmall in
lemma card_chain_lt (w : W) : #(chain S maxFam w) < θ := by
  refine WellFoundedLT.induction (motive := fun w : W => #(chain S maxFam w) < θ) w
    fun w ih => ?_
  show #(chain S maxFam w) < θ
  rw [chain_eq]
  have hY : #(⋃ v : Iio w, chain S maxFam v.1) < θ :=
    mk_iUnion_lt hθ _ ((hIio w).trans_lt hμθ) fun v => ih v.1 v.2
  exact card_Ynext_lt S hθ hμθ hS hY (hsmall _ hY)

include hθ hμθ hS hIio hsmall in
lemma card_iUnion_chain_lt (hWc : #W < θ) : #(⋃ w : W, chain S maxFam w) < θ :=
  mk_iUnion_lt hθ _ hWc fun w => card_chain_lt S hθ hμθ hS hIio hsmall w

include hθ hμθ hS hIio hsmall in
lemma chain_contradiction (hμ : ℵ₀ ≤ μ) (hW : ¬ #W ≤ μ)
    (hmeets : ∀ Y : Set ι, #Y < θ → ∀ a, ¬ S a ⊆ Y → (S a ∩ (Ynext S maxFam Y \ Y)).Nonempty)
    (a : A) (ha : ¬ S a ⊆ ⋃ w : W, chain S maxFam w) : False := by
  classical
  have hex : ∀ e : ↥(S a ∩ ⋃ w : W, chain S maxFam w), ∃ w, (e : ι) ∈ chain S maxFam w :=
    fun e => mem_iUnion.mp e.2.2
  choose wf hwf using hex
  have hrange : #(range wf) ≤ μ :=
    mk_range_le.trans ((mk_le_mk_of_subset inter_subset_left).trans (hS a))
  obtain ⟨w₀, hw₀⟩ := exists_upper_bound_of_small hμ hW hIio hrange
  have hsub : S a ∩ ⋃ w : W, chain S maxFam w ⊆ chain S maxFam w₀ := fun e he =>
    chain_mono S maxFam (hw₀ _ ⟨⟨e, he⟩, rfl⟩) (hwf ⟨e, he⟩)
  obtain ⟨w₁, hw₁⟩ := exists_gt_of_large hμ hW hIio w₀
  have hY₀ : chain S maxFam w₀ ⊆ ⋃ v : Iio w₁, chain S maxFam v.1 :=
    subset_iUnion (fun v : Iio w₁ => chain S maxFam v.1) ⟨w₀, hw₁⟩
  have hYX : (⋃ v : Iio w₁, chain S maxFam v.1) ⊆ ⋃ w : W, chain S maxFam w :=
    iUnion_subset fun v => subset_iUnion (fun w => chain S maxFam w) v.1
  have hnot : ¬ S a ⊆ ⋃ v : Iio w₁, chain S maxFam v.1 := fun h => ha (h.trans hYX)
  have hYc : #(⋃ v : Iio w₁, chain S maxFam v.1) < θ :=
    mk_iUnion_lt hθ _ ((hIio w₁).trans_lt hμθ) fun v =>
      card_chain_lt S hθ hμθ hS hIio hsmall v.1
  obtain ⟨e, heS, heX, heY⟩ := hmeets _ hYc a hnot
  have heX' : e ∈ ⋃ w : W, chain S maxFam w := by
    rw [mem_iUnion]
    exact ⟨w₁, by rw [chain_eq]; exact heX⟩
  exact heY (hY₀ (hsub ⟨heS, heX'⟩))

end chain

/-- `μ⁺` as a type: `(succ μ).ord.ToType`. -/
lemma succ_ord_facts (μ : Cardinal.{u}) :
    ¬ #(Order.succ μ).ord.ToType ≤ μ ∧
      (∀ w : (Order.succ μ).ord.ToType, #(Iio w) ≤ μ) ∧
      #(Order.succ μ).ord.ToType = Order.succ μ := by
  refine ⟨?_, ?_, mk_ord_toType _⟩
  · rw [mk_ord_toType]
    exact (Order.lt_succ μ).not_ge
  · intro w
    have h1 : #(Iio w) < #(Order.succ μ).ord.ToType :=
      Cardinal.mk_Iio_lt w (by rw [Cardinal.mk_ord_toType, Ordinal.type_toType])
    rw [mk_ord_toType] at h1
    exact Order.lt_succ_iff.mp h1

/-- **General Δ-system lemma** (ZFC).  Let `μ` be infinite and `θ` regular with
`ν ^ μ < θ` for all `ν < θ`.  Any family `S : A → Set ι` of sets of size `≤ μ` indexed by a type
of cardinality `θ` has a Δ-subsystem of cardinality `θ`: there are `J` with `#J = θ` and a root
`R` with `R ⊆ S a` (`a ∈ J`) and `S a ∩ S b = R` for distinct `a, b ∈ J`. -/
theorem delta_system (hμ : ℵ₀ ≤ μ) (hθ : θ.IsRegular) (hpow : ∀ ν < θ, ν ^ μ < θ)
    (hS : ∀ a, #(S a) ≤ μ) (hA : #A = θ) :
    ∃ (J : Set A) (R : Set ι), #J = θ ∧ (∀ a ∈ J, R ⊆ S a) ∧
      ∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R := by
  classical
  have hμθ : μ < θ := lt_of_pow_hyp hθ hpow
  by_contra hno
  have hsmall' : ∀ Y : Set ι, #Y < θ → ∀ F : Set A, DisjOutside S Y F → #F < θ := by
    intro Y hY F hF
    by_contra h
    exact hno (exists_delta_of_disjOutside S hμ hθ hpow hS hA hY (not_lt.mp h) hF)
  choose maxFam hmax using exists_maximal_fam S
  have hsmall : ∀ Y : Set ι, #Y < θ → #(maxFam Y) < θ := fun Y hY =>
    hsmall' Y hY _ (hmax Y).prop.2
  have hmeets : ∀ Y : Set ι, #Y < θ → ∀ a, ¬ S a ⊆ Y →
      (S a ∩ (Ynext S maxFam Y \ Y)).Nonempty := fun Y _ a ha =>
    meets_of_maximal S (hmax Y) a ha
  obtain ⟨hW, hIio, hWc⟩ := succ_ord_facts μ
  have hWθ : #(Order.succ μ).ord.ToType < θ := by
    rw [hWc]
    exact lt_of_le_of_lt (Order.succ_le_of_lt (cantor μ))
      (hpow 2 ((ofNat_lt_aleph0 : (2 : Cardinal.{u}) < ℵ₀).trans_le hθ.aleph0_le))
  have hXc := card_iUnion_chain_lt S hθ hμθ hS hIio hsmall hWθ
  have hex : ∃ a, ¬ S a ⊆ ⋃ w : (Order.succ μ).ord.ToType, chain S maxFam w := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hdisj : DisjOutside S
        (⋃ w : (Order.succ μ).ord.ToType, chain S maxFam w) univ := by
      intro a _ b _ _
      rw [Set.sdiff_eq_empty.mpr (h a)]
      exact disjoint_bot_left
    have := hsmall' _ hXc univ hdisj
    rw [Cardinal.mk_univ, hA] at this
    exact lt_irrefl _ this
  obtain ⟨a, ha⟩ := hex
  exact chain_contradiction S hθ hμθ hS hIio hsmall hμ hW hmeets a ha

/-- Δ-system lemma for an index type of cardinality `≥ θ`. -/
theorem delta_system_of_le (hμ : ℵ₀ ≤ μ) (hθ : θ.IsRegular) (hpow : ∀ ν < θ, ν ^ μ < θ)
    (hS : ∀ a, #(S a) ≤ μ) (hA : θ ≤ #A) :
    ∃ (J : Set A) (R : Set ι), #J = θ ∧ (∀ a ∈ J, R ⊆ S a) ∧
      ∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R := by
  obtain ⟨p, -, hp⟩ := le_mk_iff_exists_subset.mp (by rwa [mk_univ] : θ ≤ #(univ : Set A))
  obtain ⟨J', R, hJ', hR, hΔ⟩ :=
    delta_system (fun a : p => S a.1) hμ hθ hpow (fun a => hS a.1) hp
  refine ⟨Subtype.val '' J', R, by rw [mk_image_eq Subtype.val_injective, hJ'], ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hR a ha
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact hΔ a ha b hb fun h => hab (congrArg Subtype.val h)

end Core

/-! ### Specialization `θ = (2^μ)⁺` (no GCH) -/

lemma two_pow_facts {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    (Order.succ ((2 : Cardinal.{u}) ^ μ)).IsRegular ∧
      ∀ ν < Order.succ ((2 : Cardinal.{u}) ^ μ), ν ^ μ < Order.succ ((2 : Cardinal.{u}) ^ μ) := by
  have h2 : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  refine ⟨isRegular_succ h2, fun ν hν => ?_⟩
  have hν' : ν ≤ 2 ^ μ := Order.lt_succ_iff.mp hν
  apply Order.lt_succ_iff.mpr
  calc ν ^ μ ≤ (2 ^ μ) ^ μ := power_le_power_right hν'
    _ = 2 ^ (μ * μ) := (power_mul).symm
    _ = 2 ^ μ := by rw [mul_eq_self hμ]

/-- **Δ-system lemma for `(2^μ)⁺` sets of size `≤ μ`** (ZFC, no GCH). -/
theorem delta_system_two_pow {A ι : Type u} (S : A → Set ι) {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hS : ∀ a, #(S a) ≤ μ) (hA : Order.succ (2 ^ μ) ≤ #A) :
    ∃ (J : Set A) (R : Set ι), #J = Order.succ (2 ^ μ) ∧ (∀ a ∈ J, R ⊆ S a) ∧
      ∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R :=
  delta_system_of_le S hμ (two_pow_facts hμ).1 (two_pow_facts hμ).2 hS hA


/-- The Δ-system lemma for `(2^μ)⁺` sets of size `≤ μ`, phrased with Flypitch's `IsDeltaSystem`. -/
theorem isDeltaSystem_two_pow {A ι : Type u} (S : A → Set ι) {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hS : ∀ a, #(S a) ≤ μ) (hA : Order.succ (2 ^ μ) ≤ #A) :
    ∃ J : Set A, #J = Order.succ (2 ^ μ) ∧ IsDeltaSystem (fun a : J => S a.1) := by
  obtain ⟨J, R, hJ, -, hΔ⟩ := delta_system_two_pow S hμ hS hA
  exact ⟨J, hJ, R, fun x y hxy => hΔ x.1 x.2 y.1 y.2 fun h => hxy (Subtype.ext h)⟩

/-! ### Counting blueprints -/

/-- A family of types indexed by the ordinals `< μ⁺`, each of size `≤ 2^μ`, has total size
`≤ 2^μ` (lifted to the universe of `Ordinal.{u}`). -/
theorem mk_sigma_Iio_succ_ord_le {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (X : Ordinal.{u} → Type u)
    (hX : ∀ α < (Order.succ μ).ord, #(X α) ≤ 2 ^ μ) :
    #(Σ α : Iio (Order.succ μ).ord, X α.1) ≤ Cardinal.lift.{u + 1} (2 ^ μ) := by
  have h2 : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hι : #(Iio (Order.succ μ).ord) ≤ Cardinal.lift.{u + 1} (2 ^ μ) := by
    rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord, Cardinal.lift_le]
    exact Order.succ_le_of_lt (cantor μ)
  rw [mk_sigma]
  calc sum (fun α : Iio (Order.succ μ).ord => #(X α.1))
      ≤ Cardinal.lift.{u} #(Iio (Order.succ μ).ord) *
          ⨆ α : Iio (Order.succ μ).ord, Cardinal.lift.{u + 1} #(X α.1) :=
        sum_le_lift_mk_mul_iSup_lift _
    _ ≤ Cardinal.lift.{u + 1} (2 ^ μ) * Cardinal.lift.{u + 1} (2 ^ μ) := by
        refine mul_le_mul' ?_ (ciSup_le' fun α => Cardinal.lift_le.mpr (hX α.1 α.2))
        simpa using hι
    _ = Cardinal.lift.{u + 1} (2 ^ μ) := by rw [← Cardinal.lift_mul, mul_eq_self h2]

lemma card_lt_succ_ord_iff {μ : Cardinal.{u}} {α : Ordinal.{u}} :
    α < (Order.succ μ).ord ↔ α.card ≤ μ := by
  rw [Cardinal.lt_ord, Order.lt_succ_iff]

/-- Functions from a set of size `≤ μ` into a set of size `≤ 2^μ`: at most `2^μ`. -/
lemma mk_arrow_le_two_pow {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) {T D : Type u}
    (hT : #T ≤ μ) (hD : #D ≤ 2 ^ μ) : #(T → D) ≤ 2 ^ μ := by
  rw [← power_def]
  calc #D ^ #T ≤ (2 ^ μ) ^ #T := power_le_power_right hD
    _ ≤ (2 ^ μ) ^ μ := power_le_power_left (power_ne_zero _ two_ne_zero) hT
    _ = 2 ^ μ := by rw [← power_mul, mul_eq_self hμ]

lemma mk_rel_le_two_pow {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) {T : Type u} (hT : #T ≤ μ) :
    #(T → T → Prop) ≤ 2 ^ μ := by
  have h1 : #(T → Prop) ≤ 2 ^ μ := by
    show #(Set T) ≤ 2 ^ μ
    rw [mk_set]
    exact power_le_power_left two_ne_zero hT
  exact mk_arrow_le_two_pow hμ hT h1

/-- Blueprints: an order type `α < μ⁺` together with a binary relation and a `D`-colouring on it. -/
abbrev Blueprint (μ : Cardinal.{u}) (D : Type u) : Type (u + 1) :=
  Σ α : Iio (Order.succ μ).ord, (α.1.ToType → α.1.ToType → Prop) × (α.1.ToType → D)

/-- **Counting blueprints**: there are at most `2^μ` of them (for `#D ≤ 2^μ`). -/
theorem mk_blueprint_le {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (D : Type u) (hD : #D ≤ 2 ^ μ) :
    #(Blueprint μ D) ≤ Cardinal.lift.{u + 1} (2 ^ μ) := by
  have h2 : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  refine mk_sigma_Iio_succ_ord_le hμ
    (fun α => (α.ToType → α.ToType → Prop) × (α.ToType → D)) fun α hα => ?_
  have hT : #α.ToType ≤ μ := by rw [mk_toType]; exact card_lt_succ_ord_iff.mp hα
  rw [← mul_def]
  calc #(α.ToType → α.ToType → Prop) * #(α.ToType → D) ≤ 2 ^ μ * 2 ^ μ :=
        mul_le_mul' (mk_rel_le_two_pow hμ hT) (mk_arrow_le_two_pow hμ hT hD)
    _ = 2 ^ μ := mul_eq_self h2

/-- Relation-only blueprints: at most `2^μ`. -/
theorem mk_rel_blueprint_le {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    #(Σ α : Iio (Order.succ μ).ord, (α.1.ToType → α.1.ToType → Prop)) ≤
      Cardinal.lift.{u + 1} (2 ^ μ) :=
  mk_sigma_Iio_succ_ord_le hμ (fun α => α.ToType → α.ToType → Prop) fun α hα =>
    mk_rel_le_two_pow hμ (by rw [mk_toType]; exact card_lt_succ_ord_iff.mp hα)

/-- The order type of a set of size `≤ μ` in a well-order is `< μ⁺`. -/
lemma type_lt_succ_ord {W : Type u} [LinearOrder W] [WellFoundedLT W] {μ : Cardinal.{u}}
    (s : Set W) (hs : #s ≤ μ) :
    Ordinal.type (α := s) (· < ·) < (Order.succ μ).ord := by
  rw [card_lt_succ_ord_iff, Ordinal.card_type]
  exact hs

/-! ### Pigeonhole -/

/-- **Pigeonhole** (θ regular): a map from a type of size `≥ θ` into a type of size `< θ`
(sizes compared after lifting to a common universe) is constant on a set of size exactly `θ`. -/
theorem exists_const_on_large {A : Type u} {X : Type v} {θ : Cardinal.{u}} (hθ : θ.IsRegular)
    (hA : θ ≤ #A) (f : A → X) (hX : Cardinal.lift.{u} #X < Cardinal.lift.{v} θ) :
    ∃ J : Set A, #J = θ ∧ ∀ a ∈ J, ∀ b ∈ J, f a = f b := by
  obtain ⟨c, hc⟩ : Cardinal.lift.{u} #X ∈ Set.range Cardinal.lift.{v, u} :=
    Cardinal.mem_range_lift_of_le hX.le
  have hcθ : c < θ := Cardinal.lift_lt.mp (hc ▸ hX)
  obtain ⟨e⟩ : Nonempty (X ↪ c.out) := by
    rw [← Cardinal.lift_mk_le', mk_out, hc]
  obtain ⟨y, hy⟩ := Cardinal.infinite_pigeonhole_card (fun a => e (f a)) θ hA hθ.aleph0_le
    (by rw [hθ.cof_ord, mk_out]; exact hcθ)
  obtain ⟨J, hJsub, hJ⟩ := le_mk_iff_exists_subset.mp hy
  refine ⟨J, hJ, fun a ha b hb => e.injective ?_⟩
  have ha' : e (f a) = y := hJsub ha
  have hb' : e (f b) = y := hJsub hb
  rw [ha', hb']

/-! ### The chain-condition skeleton -/

/-- **cc skeleton (general θ)**: given `θ` indices, a "blueprint" map `f` into a type of size
`< θ`, and sets `S a` of size `≤ μ`, there is a set `J` of size `θ` on which `f` is constant and
`S` forms a Δ-system with root `R`. -/
theorem cc_skeleton {A ι : Type u} {X : Type v} {μ θ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hθ : θ.IsRegular) (hpow : ∀ ν < θ, ν ^ μ < θ) (hA : θ ≤ #A)
    (f : A → X) (hX : Cardinal.lift.{u} #X < Cardinal.lift.{v} θ)
    (S : A → Set ι) (hS : ∀ a, #(S a) ≤ μ) :
    ∃ (J : Set A) (R : Set ι), #J = θ ∧ (∀ a ∈ J, ∀ b ∈ J, f a = f b) ∧
      (∀ a ∈ J, R ⊆ S a) ∧ ∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R := by
  obtain ⟨J₀, hJ₀, hf⟩ := exists_const_on_large hθ hA f hX
  obtain ⟨J', R, hJ', hR, hΔ⟩ :=
    delta_system (fun a : J₀ => S a.1) hμ hθ hpow (fun a => hS a.1) hJ₀
  refine ⟨Subtype.val '' J', R, by rw [mk_image_eq Subtype.val_injective, hJ'], ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact hf a.1 a.2 b.1 b.2
  · rintro _ ⟨a, ha, rfl⟩
    exact hR a ha
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact hΔ a ha b hb fun h => hab (congrArg Subtype.val h)

/-- **cc skeleton for `θ = (2^μ)⁺`** (ZFC, no GCH): blueprint map into a type of size `≤ 2^μ`. -/
theorem cc_skeleton_two_pow {A ι : Type u} {X : Type v} {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hA : Order.succ (2 ^ μ) ≤ #A) (f : A → X)
    (hX : Cardinal.lift.{u} #X ≤ Cardinal.lift.{v} (2 ^ μ))
    (S : A → Set ι) (hS : ∀ a, #(S a) ≤ μ) :
    ∃ (J : Set A) (R : Set ι), #J = Order.succ (2 ^ μ) ∧ (∀ a ∈ J, ∀ b ∈ J, f a = f b) ∧
      (∀ a ∈ J, R ⊆ S a) ∧ ∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R :=
  cc_skeleton hμ (two_pow_facts hμ).1 (two_pow_facts hμ).2 hA f
    (hX.trans_lt (by rw [Cardinal.lift_lt]; exact Order.lt_succ _)) S hS

/-- **cc pair form**: among `(2^μ)⁺` indices there are two distinct ones with the same blueprint
whose supports meet exactly in the common root `R` (which lies in both). -/
theorem cc_pair_two_pow {A ι : Type u} {X : Type v} {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hA : Order.succ (2 ^ μ) ≤ #A) (f : A → X)
    (hX : Cardinal.lift.{u} #X ≤ Cardinal.lift.{v} (2 ^ μ))
    (S : A → Set ι) (hS : ∀ a, #(S a) ≤ μ) :
    ∃ (R : Set ι) (a b : A), a ≠ b ∧ f a = f b ∧ S a ∩ S b = R := by
  obtain ⟨J, R, hJ, hf, hR, hΔ⟩ := cc_skeleton_two_pow hμ hA f hX S hS
  have h2 : (2 : Cardinal) ≤ #J := by
    rw [hJ]
    exact ((ofNat_lt_aleph0 : (2 : Cardinal.{u}) < ℵ₀).le.trans
      (hμ.trans (cantor μ).le)).trans (Order.le_succ _)
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := two_le_iff.mp h2
  have hab' : a ≠ b := fun h => hab (Subtype.ext h)
  exact ⟨R, a, b, hab', hf a ha b hb, hΔ a ha b hb hab'⟩


/-! ### Root-fixing refinement

With a well-order on the coordinates, we can further arrange that all supports have the same
order type and that **every** order isomorphism between two of them fixes the root pointwise
(the form used in the `(2^μ)⁺`-c.c. argument of Sh:258 §3.8). -/

section RootFix

/-- Position of `x ∈ s` in the well-ordered set `s`. -/
noncomputable def pos {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] (s : Set ι) (x : s) :
    Ordinal.{u} :=
  Ordinal.typein (α := s) (· < ·) x

lemma pos_lt_type {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] (s : Set ι) (x : s) :
    pos s x < Ordinal.type (α := s) (· < ·) :=
  Ordinal.typein_lt_type (α := s) (· < ·) x

/-- Order isomorphisms preserve positions. -/
lemma pos_orderIso {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s t : Set ι} (e : s ≃o t)
    (x : s) : pos t (e x) = pos s x :=
  Ordinal.typein_apply (α := s) (β := t) e.toRelIsoLT.toInitialSeg x

/-- An order isomorphism fixes every point sitting at the same position in both sets. -/
lemma orderIso_fix {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s t : Set ι} (e : s ≃o t)
    {r : ι} (hs : r ∈ s) (ht : r ∈ t)
    (hpos : pos s ⟨r, hs⟩ = pos t ⟨r, ht⟩) : (e ⟨r, hs⟩ : ι) = r := by
  have h : pos t (e ⟨r, hs⟩) = pos t ⟨r, ht⟩ := by rw [pos_orderIso, hpos]
  exact congrArg Subtype.val ((Ordinal.typein_injective (α := t) (· < ·)) h)

variable {ι : Type u} [LinearOrder ι] [WellFoundedLT ι]

lemma mk_Iio_succ_ord_le {μ : Cardinal.{u}} :
    #(Iio (Order.succ μ).ord) ≤ Cardinal.lift.{u + 1} (2 ^ μ) := by
  rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord, Cardinal.lift_le]
  exact Order.succ_le_of_lt (cantor μ)

omit [LinearOrder ι] [WellFoundedLT ι] in
lemma mk_rootData_le {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (R : Set ι) (hR : #R ≤ μ) :
    #(Iio (Order.succ μ).ord × (R → Iio (Order.succ μ).ord)) ≤
      Cardinal.lift.{u + 1} (2 ^ μ) := by
  have h2 : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have harr : #(R → Iio (Order.succ μ).ord) ≤ Cardinal.lift.{u + 1} (2 ^ μ) := by
    rw [Cardinal.mk_arrow]
    calc Cardinal.lift.{u} #(Iio (Order.succ μ).ord) ^ Cardinal.lift.{u + 1} #R
        ≤ Cardinal.lift.{u + 1} (2 ^ μ) ^ Cardinal.lift.{u + 1} #R := by
          refine power_le_power_right ?_
          simpa using mk_Iio_succ_ord_le (μ := μ)
      _ ≤ Cardinal.lift.{u + 1} (2 ^ μ) ^ Cardinal.lift.{u + 1} μ :=
          power_le_power_left (by rw [Ne, Cardinal.lift_eq_zero]; exact power_ne_zero _ two_ne_zero)
            (Cardinal.lift_le.mpr hR)
      _ = Cardinal.lift.{u + 1} (2 ^ μ) := by
          rw [← Cardinal.lift_power, ← power_mul, mul_eq_self hμ]
  rw [← mul_def]
  calc #(Iio (Order.succ μ).ord) * #(R → Iio (Order.succ μ).ord)
      ≤ Cardinal.lift.{u + 1} (2 ^ μ) * Cardinal.lift.{u + 1} (2 ^ μ) :=
        mul_le_mul' mk_Iio_succ_ord_le harr
    _ = Cardinal.lift.{u + 1} (2 ^ μ) := by rw [← Cardinal.lift_mul, mul_eq_self h2]

/-- **cc skeleton with root-fixing** (`θ = (2^μ)⁺`, ZFC, no GCH).  Given `(2^μ)⁺` indices, a
blueprint map `f` into a type of size `≤ 2^μ`, and supports `S a` of size `≤ μ` in a well-ordered
type, there are `J` of size `(2^μ)⁺` and a root `R` such that on `J`: `f` is constant, the
supports form a Δ-system with root `R`, any two supports are order-isomorphic, and **every**
order isomorphism between two supports fixes `R` pointwise. -/
theorem cc_skeleton_rootfix {A : Type u} {X : Type v} {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hA : Order.succ (2 ^ μ) ≤ #A) (f : A → X)
    (hX : Cardinal.lift.{u} #X ≤ Cardinal.lift.{v} (2 ^ μ))
    (S : A → Set ι) (hS : ∀ a, #(S a) ≤ μ) :
    ∃ (J : Set A) (R : Set ι), #J = Order.succ (2 ^ μ) ∧ (∀ a ∈ J, ∀ b ∈ J, f a = f b) ∧
      (∀ a ∈ J, R ⊆ S a) ∧ (∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R) ∧
      (∀ a ∈ J, ∀ b ∈ J, Nonempty (S a ≃o S b)) ∧
      ∀ a ∈ J, ∀ b ∈ J, ∀ e : S a ≃o S b, ∀ x : S a, (x : ι) ∈ R → (e x : ι) = x := by
  obtain ⟨J₁, R, hJ₁, hf, hR, hΔ⟩ := cc_skeleton_two_pow hμ hA f hX S hS
  have hRμ : #R ≤ μ := by
    obtain ⟨⟨a, ha⟩⟩ := Cardinal.mk_ne_zero_iff.mp
      (by rw [hJ₁]; exact (zero_le.trans_lt (Order.lt_succ (2 ^ μ))).ne')
    exact (mk_le_mk_of_subset (hR a ha)).trans (hS a)
  let g : J₁ → Iio (Order.succ μ).ord × (R → Iio (Order.succ μ).ord) := fun a =>
    (⟨Ordinal.type (α := S a.1) (· < ·), type_lt_succ_ord (S a.1) (hS a.1)⟩,
     fun r => ⟨pos (S a.1) ⟨r.1, hR a.1 a.2 r.2⟩, Set.mem_Iio.mpr
       ((pos_lt_type _ _).trans (type_lt_succ_ord (S a.1) (hS a.1)))⟩)
  have hreg := (two_pow_facts hμ).1
  obtain ⟨J₂, hJ₂, hg⟩ := exists_const_on_large (θ := Order.succ (2 ^ μ)) hreg hJ₁.ge g
    (by
      refine lt_of_le_of_lt (b := Cardinal.lift.{u + 1} (2 ^ μ)) ?_ ?_
      · simpa using mk_rootData_le hμ R hRμ
      · rw [Cardinal.lift_lt]; exact Order.lt_succ _)
  refine ⟨Subtype.val '' J₂, R, by rw [mk_image_eq Subtype.val_injective, hJ₂], ?_, ?_, ?_, ?_,
    ?_⟩
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact hf a.1 a.2 b.1 b.2
  · rintro _ ⟨a, -, rfl⟩
    exact hR a.1 a.2
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ hab
    exact hΔ a.1 a.2 b.1 b.2 hab
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := congrArg (fun p => (p.1 : Ordinal.{u})) (hg a ha b hb)
    obtain ⟨e⟩ := Ordinal.type_eq.mp h1
    exact ⟨OrderIso.ofRelIsoLT e⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ e x hx
    have h2 := congrArg (fun p => ((p.2 ⟨x.1, hx⟩ : Iio (Order.succ μ).ord) : Ordinal.{u}))
      (hg a ha b hb)
    exact orderIso_fix e x.2 (hR b.1 b.2 hx) h2

end RootFix

end Erdos1220.DeltaSystem

#print axioms Erdos1220.DeltaSystem.delta_system
#print axioms Erdos1220.DeltaSystem.delta_system_of_le
#print axioms Erdos1220.DeltaSystem.delta_system_two_pow
#print axioms Erdos1220.DeltaSystem.mk_sigma_Iio_succ_ord_le
#print axioms Erdos1220.DeltaSystem.mk_blueprint_le
#print axioms Erdos1220.DeltaSystem.mk_rel_blueprint_le
#print axioms Erdos1220.DeltaSystem.type_lt_succ_ord
#print axioms Erdos1220.DeltaSystem.exists_const_on_large
#print axioms Erdos1220.DeltaSystem.cc_skeleton
#print axioms Erdos1220.DeltaSystem.cc_skeleton_two_pow
#print axioms Erdos1220.DeltaSystem.cc_pair_two_pow
#print axioms Erdos1220.DeltaSystem.orderIso_fix
#print axioms Erdos1220.DeltaSystem.cc_skeleton_rootfix
#print axioms Erdos1220.DeltaSystem.isDeltaSystem_two_pow
