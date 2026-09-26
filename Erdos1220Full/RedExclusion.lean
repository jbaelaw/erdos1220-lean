import Erdos1220Full.GenericColouring
import Erdos1220Full.CardPreserve
import Erdos1220.RedCore

/-!
# No red homogeneous set of full size in the covering-history model (Sh:258 §3.9)

Step 3b of `docs-claude/ASSEMBLY-PLAN.md`.  Over `𝔹 = CAlg x.Type I block μ hμ` (`u = 0`) with
the generic colouring `ċ = cdot x block μ hμ` of `GenericColouring.lean`, for every name `H`:

  `Γ ⊓ (Sem.subset H x̌ ⊓ (Sem.eqCard H x̌ ⊓ Sem.homog0 ċ H)) ≤ ⊥`   (`red_exclusion`)

provided `#I ≤ μ`, the vertices `x.Func v` are pairwise inequivalent, blocks are ordered
(`block a < block b → x.Func a ∈ x.Func b`), `(2^μ)⁺ < #x.Type` and every block has size
`< #x.Type`.

* **(i) small case.**  `Large b Δ'`: below every nonzero `Γ' ≤ Δ'` and outside every ground set
  `Z` of size `< θ = (2^μ)⁺`, some vertex of block `b` is possibly in `H`.  By distributivity over
  the `≤ μ` blocks, either two blocks are large below one nonzero element, or one condition pins
  `H` inside a ground set `S` with `#S · θ < #x.Type`; then `x̌ ↪ H ⊆ Š` contradicts the
  `θ`-chain condition (`leqB_check_eq_bot_of_chainCondition`).  (No use of `Sem.cardinal x̌`.)
* **(ii) large case.**  A greedy recursion of length `θ` gives conditions `p_ξ` pinning fresh
  vertices `x_ξ` (block `b₁`), `y_ξ` (block `b₂`) into `H` and into their supports;
  `BPHistory.red_core` gives a common extension `U` of two of them with `x_a`–`y_b` blue, so
  `emb U` forces the pair colour to be `1`, while `homog0` forces it to be `0`.

The `(2^μ)⁺`-chain condition of the covering forcing is proved here as well (`antichain_CHP`).
-/

open Cardinal Set Order Flypitch bSet Lattice

namespace Erdos1220Full

namespace RedExclusion

open Erdos1220 Erdos1220.BasicCondition Erdos1220.BPHistory HistoryForcing GenericColouring

/-! ## Chain condition of the covering forcing -/

section Chain

variable {V I : Type} {block : V → I} {μ : Cardinal.{0}} {hμ : ℵ₀ ≤ μ}

theorem antichain_CHP (hI : #I ≤ 2 ^ μ) :
    ∀ (ι : Type) (p : ι → CHP V I block μ hμ), Order.succ (2 ^ μ) ≤ #ι →
      ∃ i j, i ≠ j ∧ Compatible (p i) (p j) := by
  intro ι p hι
  obtain ⟨a, b, hab, e, he, hfix, -, heq⟩ :=
    HistoryBlueprint.cc_histories (hμ := hμ) hI hι (fun a => (p a).1.1)
  have hfix' : ∀ z ∈ (p a).1.1.last.support, z ∈ ((p a).1.1.relabel e he).last.support →
      e z = z := by
    intro z hz hz'
    rw [← heq] at hz'
    exact hfix z ⟨hz, hz'⟩
  obtain ⟨U, h1, h2, -⟩ := exists_red_isoAmalgam (p a).1 e he hfix'
  have hQ : relabelBP (p a).1 e he = (p b).1 := Subtype.ext heq.symm
  rw [hQ] at h2
  exact ⟨a, b, hab, ⟨U, h1.coversBlocks (p a).2⟩, h1, h2⟩

end Chain

/-! ## Boolean-valued lemmas -/

section Bool

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

theorem sem_leq_eq (A B : bSet β) : Flypitch.Erdos1220.Sem.leq A B = CardB.leqB A B := rfl

theorem sem_subset_eq (A B : bSet β) : Flypitch.Erdos1220.Sem.subset A B = CardB.subsetB A B :=
  rfl

theorem imp_sup_mono_cod {Γ F a : β} {T : bSet β → β} {l l' : bSet β}
    (h : Γ ≤ CardB.subsetB l l') (hF : F ≤ (a ⟹ ⨆ y, y ∈ᴮ l ⊓ T y)) :
    Γ ⊓ F ≤ (a ⟹ ⨆ y, y ∈ᴮ l' ⊓ T y) := by
  rw [← deduction]
  calc Γ ⊓ F ⊓ a ≤ Γ ⊓ ⨆ y, y ∈ᴮ l ⊓ T y :=
        le_inf (inf_le_left.trans inf_le_left)
          (le_trans (inf_le_inf_right a (inf_le_right.trans hF)) bv_imp_elim)
    _ = ⨆ y, Γ ⊓ (y ∈ᴮ l ⊓ T y) := inf_iSup_eq _ _
    _ ≤ ⨆ y, y ∈ᴮ l' ⊓ T y := iSup_mono fun y =>
        le_inf ((inf_le_inf_left Γ inf_le_left).trans
          (deduction.mpr (h.trans (iInf_le _ y)))) (inf_le_right.trans inf_le_right)

theorem isFunB_mono_cod {Γ : β} {D l l' f : bSet β} (h : Γ ≤ CardB.subsetB l l') :
    Γ ⊓ CardB.isFunB D l f ≤ CardB.isFunB D l' f := by
  unfold CardB.isFunB
  exact le_iInf fun a => imp_sup_mono_cod h (iInf_le _ a)

theorem leqB_mono_cod {Γ : β} {A l l' : bSet β} (h : Γ ≤ CardB.subsetB l l')
    (h2 : Γ ≤ CardB.leqB A l) : Γ ≤ CardB.leqB A l' := by
  unfold CardB.leqB at h2 ⊢
  calc Γ ≤ Γ ⊓ ⨆ f, CardB.isFunB A l f ⊓ CardB.injOnB A f := le_inf le_rfl h2
    _ = ⨆ f, Γ ⊓ (CardB.isFunB A l f ⊓ CardB.injOnB A f) := inf_iSup_eq _ _
    _ ≤ ⨆ f, CardB.isFunB A l' f ⊓ CardB.injOnB A f := iSup_mono fun f =>
        le_inf ((inf_le_inf_left Γ inf_le_left).trans (isFunB_mono_cod h))
          (inf_le_right.trans inf_le_right)

/-- `H ⊆ Š` once `H ⊆ x̌` and every vertex outside `S` is excluded from `H`. -/
theorem subsetB_of_pins (x : PSet.{0}) (H : bSet β) (S : Set x.Type) {Γ : β}
    (hsub : Γ ≤ Flypitch.Erdos1220.Sem.subset H (check x))
    (hS : ∀ v, v ∉ S → Γ ⊓ (check (x.Func v) : bSet β) ∈ᴮ H ≤ ⊥) :
    Γ ≤ CardB.subsetB H (check (PSet.mk S (fun s => x.Func s.1))) := by
  classical
  unfold CardB.subsetB
  refine le_iInf fun z => ?_
  rw [← deduction]
  have h1 : Γ ⊓ z ∈ᴮ H ≤ z ∈ᴮ (check x : bSet β) :=
    le_trans (inf_le_inf_right _ (hsub.trans (iInf_le _ z))) bv_imp_elim
  replace h1 := h1.trans (le_of_eq (mem_unfold (u := z) (v := (check x : bSet β))))
  have h2 : Γ ⊓ z ∈ᴮ H ≤ ⨆ i : (check x : bSet β).type,
      Γ ⊓ z ∈ᴮ H ⊓ z =ᴮ (check x : bSet β).func i := by
    calc Γ ⊓ z ∈ᴮ H ≤ (Γ ⊓ z ∈ᴮ H) ⊓ ⨆ i : (check x : bSet β).type,
          (check x : bSet β).bval i ⊓ z =ᴮ (check x : bSet β).func i := le_inf le_rfl h1
      _ = ⨆ i : (check x : bSet β).type, (Γ ⊓ z ∈ᴮ H) ⊓
          ((check x : bSet β).bval i ⊓ z =ᴮ (check x : bSet β).func i) := inf_iSup_eq _ _
      _ ≤ _ := iSup_mono fun i => inf_le_inf_left _ inf_le_right
  refine h2.trans (iSup_le fun i => ?_)
  have hf : (check x : bSet β).func i = check (x.Func (check_cast i)) := check_func
  rw [hf]
  by_cases hv : check_cast i ∈ S
  · exact subst_congr_mem_left' (bv_symm inf_le_right)
      (mem_check_of_mem (x := PSet.mk S (fun s => x.Func s.1)) (i := ⟨check_cast i, hv⟩))
  · have h3 : Γ ⊓ z ∈ᴮ H ⊓ z =ᴮ check (x.Func (check_cast i)) ≤
        Γ ⊓ (check (x.Func (check_cast i)) : bSet β) ∈ᴮ H :=
      le_inf (inf_le_left.trans inf_le_left)
        (subst_congr_mem_left' inf_le_right (inf_le_left.trans inf_le_right))
    exact (h3.trans (hS _ hv)).trans bot_le

/-- A red-homogeneous-type contradiction from a blue pair. -/
theorem homog0_kill (c H a b one : bSet β) {T : β} (hab : T ≤ a ∈ᴮ b)
    (hH : T ≤ Flypitch.Erdos1220.Sem.homog0 c H) (ha : T ≤ a ∈ᴮ H) (hb : T ≤ b ∈ᴮ H)
    (happ : T ≤ Flypitch.Erdos501.Sem.app c (pair a b) one) :
    T ≤ Flypitch.Erdos1220.Sem.zero one := by
  have e1 := hH.trans (iInf_le _ a)
  have e2 := le_trans (le_inf e1 ha) bv_imp_elim
  have e3 := le_trans (le_inf (e2.trans (iInf_le _ b)) hb) bv_imp_elim
  have e4 := le_trans (le_inf e3 hab) bv_imp_elim
  exact le_trans (le_inf (e4.trans (iInf_le _ one)) happ) bv_imp_elim

end Bool

/-! ## Large blocks -/

section Large

variable {β : Type} [NontrivialCompleteBooleanAlgebra β] {I : Type}

/-- Below `Γ`, `H` possibly contains vertices of block `b` outside any small ground set. -/
def Large (x : PSet.{0}) (block : x.Type → I) (H : bSet β) (θ : Cardinal.{0}) (b : I)
    (Γ : β) : Prop :=
  ∀ Γ' : β, ⊥ < Γ' → Γ' ≤ Γ → ∀ Z : Set x.Type, #Z < θ →
    ∃ v, block v = b ∧ v ∉ Z ∧ ⊥ < Γ' ⊓ (check (x.Func v) : bSet β) ∈ᴮ H

theorem Large.mono {x : PSet.{0}} {block : x.Type → I} {H : bSet β} {θ : Cardinal.{0}}
    {b : I} {Γ Γ₀ : β} (h : Large x block H θ b Γ) (hle : Γ₀ ≤ Γ) :
    Large x block H θ b Γ₀ :=
  fun Γ' hpos hΓ' Z hZ => h Γ' hpos (hΓ'.trans hle) Z hZ

/-- `H` misses block `b` outside `Z`. -/
def Pin (x : PSet.{0}) (block : x.Type → I) (H : bSet β) (b : I) (Z : Set x.Type) : β :=
  ⨅ v, ⨅ (_ : block v = b), ⨅ (_ : v ∉ Z), ((check (x.Func v) : bSet β) ∈ᴮ H)ᶜ

/-- Supremum of the elements below which block `b` is large. -/
def Lsup (x : PSet.{0}) (block : x.Type → I) (H : bSet β) (θ : Cardinal.{0}) (b : I) : β :=
  ⨆ Γ' : {Γ' : β // Large x block H θ b Γ'}, Γ'.1

end Large

/-! ## The covering model -/

section Model

variable {I : Type} {x : PSet.{0}} {block : x.Type → I} {μ : Cardinal.{0}} {hμ : ℵ₀ ≤ μ}
variable [Nonempty (CHP0 x.Type I block μ hμ)]

/-- **(i) Dichotomy.**  Either two distinct blocks are large below one nonzero element, or one
condition excludes from `H` every vertex outside one block and outside small sets `Z b`. -/
theorem two_large_or_pinned [Nonempty I] (hI : #I ≤ μ) {θ : Cardinal.{0}} (hθ : ℵ₀ ≤ θ)
    (H : bSet (CAlg x.Type I block μ hμ)) {Δ : CAlg x.Type I block μ hμ} (hΔ : ⊥ < Δ) :
    (∃ Δ' : CAlg x.Type I block μ hμ, ⊥ < Δ' ∧ Δ' ≤ Δ ∧ ∃ b₁ b₂ : I, b₁ ≠ b₂ ∧
      Large x block H θ b₁ Δ' ∧ Large x block H θ b₂ Δ') ∨
    (∃ q : CHP0 x.Type I block μ hμ, emb q ≤ Δ ∧ ∃ (b₀ : I) (Z : I → Set x.Type),
      (∀ b, #(Z b) < θ) ∧ ∀ v, block v ≠ b₀ → v ∉ Z (block v) →
        emb q ⊓ (check (x.Func v) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H ≤ ⊥) := by
  classical
  let ι : I → Type := fun _ => Option {Z : Set x.Type // #Z < θ}
  let φ : ∀ b, ι b → CAlg x.Type I block μ hμ := fun b o =>
    o.elim (Lsup x block H θ b) (fun Z => Pin x block H b Z.1)
  have hφ : ∀ b (Γ' : CAlg x.Type I block μ hμ), ⊥ < Γ' → Γ' ≤ Δ → ∃ i, ⊥ < Γ' ⊓ φ b i := by
    intro b Γ' hΓ' _
    by_cases hL : Large x block H θ b Γ'
    · refine ⟨none, ?_⟩
      have hle : Γ' ≤ Lsup x block H θ b :=
        le_iSup (fun Γ'' : {Γ'' : CAlg x.Type I block μ hμ // Large x block H θ b Γ''} =>
          Γ''.1) ⟨Γ', hL⟩
      exact lt_of_lt_of_le hΓ' (le_inf le_rfl hle)
    · simp only [Large, not_forall, not_exists, not_and] at hL
      obtain ⟨Γ'', hpos, hle, Z, hZ, hmiss⟩ := hL
      refine ⟨some ⟨Z, hZ⟩, lt_of_lt_of_le hpos (le_inf hle ?_)⟩
      show Γ'' ≤ Pin x block H b Z
      refine le_iInf fun v => le_iInf fun hv => le_iInf fun hvZ => ?_
      exact le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr
        (not_bot_lt_iff.mp (hmiss v hv hvZ)).le)
  obtain ⟨q, c, hqΔ, hqc⟩ :=
    exists_forall_of_card_leC (J := I) (Cardinal.lift_le.mpr hI) hΔ φ hφ
  by_cases htwo : ∃ b₁ b₂, b₁ ≠ b₂ ∧ c b₁ = none ∧ c b₂ = none
  · left
    obtain ⟨b₁, b₂, hne, h1, h2⟩ := htwo
    have hq1 : emb q ≤ Lsup x block H θ b₁ := by
      have := hqc b₁; rw [h1] at this; exact this
    have hq2 : emb q ≤ Lsup x block H θ b₂ := by
      have := hqc b₂; rw [h2] at this; exact this
    obtain ⟨⟨Γ₁, hL₁⟩, hp₁⟩ := nonzero_inf_of_nonzero_le_supr (emb_pos q) hq1
    obtain ⟨⟨Γ₂, hL₂⟩, hp₂⟩ :=
      nonzero_inf_of_nonzero_le_supr hp₁ ((inf_le_left.trans hq2 :
        emb q ⊓ Γ₁ ≤ Lsup x block H θ b₂))
    refine ⟨emb q ⊓ Γ₁ ⊓ Γ₂, hp₂, (inf_le_left.trans inf_le_left).trans hqΔ, b₁, b₂, hne,
      hL₁.mono (inf_le_left.trans inf_le_right), hL₂.mono inf_le_right⟩
  · right
    push Not at htwo
    let b₀ : I := if h : ∃ b, c b = none then Classical.choose h else Classical.arbitrary I
    have hb₀ : ∀ b, c b = none → b = b₀ := by
      intro b hb
      have hex : ∃ b, c b = none := ⟨b, hb⟩
      have hb₀def : b₀ = Classical.choose hex := dif_pos hex
      by_contra hne
      exact htwo b b₀ hne hb (hb₀def ▸ Classical.choose_spec hex)
    refine ⟨q, hqΔ, b₀, fun b => (c b).elim ∅ Subtype.val, ?_, ?_⟩
    · intro b
      show #((c b).elim ∅ Subtype.val : Set x.Type) < θ
      cases hcb : c b with
      | none => simpa using aleph0_pos.trans_le hθ
      | some Z => exact Z.2
    · intro v hv hvZ
      cases hcb : c (block v) with
      | none => exact absurd (hb₀ _ hcb) hv
      | some Z =>
        have hq := hqc (block v)
        rw [hcb] at hq
        have hq' : emb q ≤ Pin x block H (block v) Z.1 := hq
        have hvZ' : v ∉ Z.1 := by simpa [hcb] using hvZ
        have hc : emb q ≤ ((check (x.Func v) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H)ᶜ :=
          le_trans hq' (le_trans (iInf_le _ v) (le_trans (iInf_le _ rfl) (iInf_le _ hvZ')))
        exact (inf_le_inf_right _ hc).trans (compl_inf_self _).le

/-- **(i) Small case contradiction** via the chain condition. -/
theorem pinned_contra {θ : Cardinal.{0}} (hcc : ChainCondition θ (CAlg x.Type I block μ hμ))
    (hx : ∀ i j, i ≠ j → ¬ PSet.Equiv (x.Func i) (x.Func j))
    (H : bSet (CAlg x.Type I block μ hμ)) (S : Set x.Type)
    (hfib : ∀ g : x.Type → S, ∃ ξ, θ ≤ #(g ⁻¹' {ξ}))
    {Γ : CAlg x.Type I block μ hμ} (hΓ : ⊥ < Γ)
    (hS : ∀ v, v ∉ S → Γ ⊓ (check (x.Func v) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H ≤ ⊥)
    (hsub : Γ ≤ Flypitch.Erdos1220.Sem.subset H (check x))
    (hleq : Γ ≤ CardB.leqB (check x) H) : False := by
  have h1 := subsetB_of_pins x H S hsub hS
  have h2 := leqB_mono_cod h1 hleq
  rw [CardB.leqB_check_eq_bot_of_chainCondition hcc (PSet.mk S (fun s => x.Func s.1)) x hx
    hfib] at h2
  exact absurd (lt_of_lt_of_le hΓ h2) (lt_irrefl _)

/-- Fibers of maps into a small set. -/
theorem exists_large_fiber_of_small {α : Type} {S : Set α} {θ : Cardinal.{0}}
    (hS : #S * θ < #α) (g : α → S) : ∃ ξ, θ ≤ #(g ⁻¹' {ξ}) := by
  by_contra h
  push Not at h
  exact absurd ((mk_le_mk_mul_of_mk_preimage_le g fun ξ => (h ξ).le).trans_lt hS) (lt_irrefl _)

/-! ## (ii) The large case -/

/-- Greedy recursion of length `W` choosing fresh pairs. -/
theorem exists_fresh_seq {W α γ : Type} [LinearOrder W] [WellFoundedLT W] {θ : Cardinal.{0}}
    (hθ : ℵ₀ ≤ θ) (hW : ∀ w : W, #(Iio w) < θ) (P : α → α → γ → Prop)
    (hstep : ∀ Z : Set α, #Z < θ → ∃ v w g, v ∉ Z ∧ w ∉ Z ∧ P v w g) :
    ∃ (xs ys : W → α) (gs : W → γ), Function.Injective xs ∧ Function.Injective ys ∧
      ∀ ξ, P (xs ξ) (ys ξ) (gs ξ) := by
  classical
  have h0 : #(∅ : Set α) < θ := by simpa using aleph0_pos.trans_le hθ
  choose fv fw fg hfv hfw hP using fun Z : {Z : Set α // #Z < θ} => hstep Z.1 Z.2
  let G : Set α → {Z : Set α // #Z < θ} := fun Z =>
    if h : #Z < θ then ⟨Z, h⟩ else ⟨∅, h0⟩
  let seq : W → α × α := WellFounded.fix (wellFounded_lt (α := W)) fun ξ rec =>
    (fv (G (range (fun η : Iio ξ => (rec η.1 η.2).1) ∪
        range (fun η : Iio ξ => (rec η.1 η.2).2))),
     fw (G (range (fun η : Iio ξ => (rec η.1 η.2).1) ∪
        range (fun η : Iio ξ => (rec η.1 η.2).2))))
  let Zs : W → Set α := fun ξ =>
    range (fun η : Iio ξ => (seq η.1).1) ∪ range (fun η : Iio ξ => (seq η.1).2)
  have hseq : ∀ ξ, seq ξ = (fv (G (Zs ξ)), fw (G (Zs ξ))) := fun ξ =>
    WellFounded.fix_eq _ _ ξ
  have hZs : ∀ ξ, #(Zs ξ) < θ := fun ξ =>
    (mk_union_le _ _).trans_lt
      (add_lt_of_lt hθ (mk_range_le.trans_lt (hW ξ)) (mk_range_le.trans_lt (hW ξ)))
  have hG : ∀ ξ, G (Zs ξ) = ⟨Zs ξ, hZs ξ⟩ := fun ξ => dif_pos (hZs ξ)
  have hx1 : ∀ ξ, (seq ξ).1 ∉ Zs ξ := by
    intro ξ
    rw [hseq ξ]
    have := hfv (G (Zs ξ))
    rw [hG ξ] at this ⊢
    exact this
  have hy1 : ∀ ξ, (seq ξ).2 ∉ Zs ξ := by
    intro ξ
    rw [hseq ξ]
    have := hfw (G (Zs ξ))
    rw [hG ξ] at this ⊢
    exact this
  have inj : ∀ f : W → α, (∀ η ξ, η < ξ → f η ∈ Zs ξ) → (∀ ξ, f ξ ∉ Zs ξ) →
      Function.Injective f := by
    intro f hmem hnot η ξ h
    rcases lt_trichotomy η ξ with hlt | heq | hgt
    · exact absurd (h ▸ hmem η ξ hlt) (hnot ξ)
    · exact heq
    · exact absurd (h.symm ▸ hmem ξ η hgt) (hnot η)
  refine ⟨fun ξ => (seq ξ).1, fun ξ => (seq ξ).2, fun ξ => fg (G (Zs ξ)),
    inj _ (fun η ξ h => Or.inl ⟨⟨η, h⟩, rfl⟩) hx1,
    inj _ (fun η ξ h => Or.inr ⟨⟨η, h⟩, rfl⟩) hy1, fun ξ => ?_⟩
  have := hP (G (Zs ξ))
  show P (seq ξ).1 (seq ξ).2 (fg (G (Zs ξ)))
  rw [hseq ξ]
  exact this

/-- **(ii) Two large blocks give a blue pair inside `H`.** -/
theorem blue_pair_of_two_large (hI : #I ≤ 2 ^ μ)
    (H : bSet (CAlg x.Type I block μ hμ)) {Δ' : CAlg x.Type I block μ hμ} (hpos : ⊥ < Δ')
    {b₁ b₂ : I} (hne : b₁ ≠ b₂)
    (h1 : Large x block H (Order.succ (2 ^ μ)) b₁ Δ')
    (h2 : Large x block H (Order.succ (2 ^ μ)) b₂ Δ') :
    ∃ (r : CHP0 x.Type I block μ hμ) (a b : x.Type), block a = b₁ ∧ block b = b₂ ∧
      a ∈ r.last.support ∧ b ∈ r.last.support ∧ r.last.blue a b ∧
      emb r ≤ Δ' ⊓ ((check (x.Func a) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H ⊓
        (check (x.Func b) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H) := by
  classical
  set θ : Cardinal.{0} := Order.succ (2 ^ μ) with hθdef
  have hθ : ℵ₀ ≤ θ := (hμ.trans (cantor μ).le).trans (Order.le_succ _)
  let P : x.Type → x.Type → CHP0 x.Type I block μ hμ → Prop := fun v w g =>
    block v = b₁ ∧ block w = b₂ ∧ v ∈ g.last.support ∧ w ∈ g.last.support ∧
      emb g ≤ Δ' ⊓ ((check (x.Func v) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H ⊓
        (check (x.Func w) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H)
  have hstep : ∀ Z : Set x.Type, #Z < θ → ∃ v w g, v ∉ Z ∧ w ∉ Z ∧ P v w g := by
    intro Z hZ
    obtain ⟨v, hv, hvZ, hp1⟩ := h1 Δ' hpos le_rfl Z hZ
    obtain ⟨p1, hp1'⟩ := exists_emb_le hp1
    obtain ⟨w, hw, hwZ, hp2⟩ := h2 (emb p1) (emb_pos p1) (hp1'.trans inf_le_left) Z hZ
    obtain ⟨p2, hp2'⟩ := exists_emb_le hp2
    obtain ⟨r1, hr1, hvr1⟩ := p2.exists_le_mem v
    obtain ⟨r, hr, hwr⟩ := r1.exists_le_mem w
    have hvr : v ∈ r.last.support := (CHP0.last_extends hr).1 hvr1
    have hr2 : emb r ≤ emb p2 := emb_mono (le_trans hr hr1)
    refine ⟨v, w, r, hvZ, hwZ, hv, hw, hvr, hwr, ?_⟩
    have hA : emb r ≤ emb p1 := hr2.trans (hp2'.trans inf_le_left)
    exact le_inf (hA.trans (hp1'.trans inf_le_left))
      (le_inf (hA.trans (hp1'.trans inf_le_right)) (hr2.trans (hp2'.trans inf_le_right)))
  have hW : ∀ w : θ.ord.ToType, #(Iio w) < θ := by
    intro w
    have h := Cardinal.mk_Iio_lt w (by rw [Cardinal.mk_ord_toType, Ordinal.type_toType])
    rwa [Cardinal.mk_ord_toType] at h
  obtain ⟨xs, ys, gs, hxinj, hyinj, hP⟩ :=
    exists_fresh_seq (W := θ.ord.ToType) hθ hW P hstep
  let Hs : θ.ord.ToType → BPHistory x.Type I block μ hμ := fun a => (toCHP0.symm (gs a)).1
  obtain ⟨a, b, -, U, hUa, hUb, hblue⟩ := red_core (hμ := hμ) hI
    (by rw [Cardinal.mk_ord_toType]) Hs xs ys (fun a => (hP a).2.2.1)
    (fun a => (hP a).2.2.2.1) hxinj hyinj
    (fun a b h => hne (((hP a).1.symm.trans h).trans (hP b).2.1))
  have hcov : CoversBlocks U.1.last := hUa.coversBlocks (toCHP0.symm (gs a)).2
  let U' : CHP x.Type I block μ hμ := ⟨U, hcov⟩
  let r : CHP0 x.Type I block μ hμ := toCHP0 U'
  have hle : ∀ c, WeakExtends (Hs c) U → r ≤ gs c := by
    intro c hc
    have hq : gs c = toCHP0 (toCHP0.symm (gs c)) := (Equiv.apply_symm_apply _ _).symm
    rw [hq]
    exact toCHP0_le_iff.mpr hc
  have hrU : toCHP0.symm r = U' := Equiv.symm_apply_apply _ _
  have hrlast : r.last = U.1.last := by
    show (toCHP0.symm r).1.1.last = U.1.last
    rw [hrU]
  have hra := emb_mono (hle a hUa)
  have hrb := emb_mono (hle b hUb)
  have hxa := (hP a).2.2.2.2
  have hyb := (hP b).2.2.2.2
  refine ⟨r, xs a, ys b, (hP a).1, (hP b).2.1, ?_, ?_, ?_, ?_⟩
  · rw [hrlast]; exact (U.1.last.blue_support hblue).1
  · rw [hrlast]; exact (U.1.last.blue_support hblue).2
  · rw [hrlast]; exact hblue
  · exact le_inf (hra.trans (hxa.trans inf_le_left))
      (le_inf (hra.trans (hxa.trans (inf_le_right.trans inf_le_left)))
        (hrb.trans (hyb.trans (inf_le_right.trans inf_le_right))))

/-- A decided blue pair is coloured `1` by the generic colouring. -/
theorem emb_le_app_blue {r : CHP0 x.Type I block μ hμ} {a b : x.Type}
    (hab : x.Func a ∈ x.Func b) (ha : a ∈ r.last.support) (hb : b ∈ r.last.support)
    (hblue : r.last.blue a b) :
    emb r ≤ Flypitch.Erdos501.Sem.app (cdot x block μ hμ)
      (pair (check (x.Func a)) (check (x.Func b))) (blueName x block μ hμ) := by
  have hdec : Decides x block μ hμ r a b true := ⟨ha, hb, by simp [hblue]⟩
  exact le_mem_cdot (c := true) hab (emb_le_colVal hdec) bv_refl

/-! ## The theorem -/

/-- **No red homogeneous set of size `λ`** in the covering-history model with the generic
colouring. -/
theorem red_exclusion [LinearOrder I] (hI : #I ≤ μ)
    (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    (hord : ∀ a b, block a < block b → x.Func a ∈ x.Func b)
    (hθx : Order.succ (2 ^ μ) < #x.Type) (hblk : ∀ b : I, #(block ⁻¹' {b}) < #x.Type)
    (H : bSet (CAlg x.Type I block μ hμ)) (Γ : CAlg x.Type I block μ hμ) :
    Γ ⊓ (Flypitch.Erdos1220.Sem.subset H (check x) ⊓
      (Flypitch.Erdos1220.Sem.eqCard H (check x) ⊓
        Flypitch.Erdos1220.Sem.homog0 (cdot x block μ hμ) H)) ≤ ⊥ := by
  classical
  set θ : Cardinal.{0} := Order.succ (2 ^ μ) with hθdef
  set Δ := Γ ⊓ (Flypitch.Erdos1220.Sem.subset H (check x) ⊓
      (Flypitch.Erdos1220.Sem.eqCard H (check x) ⊓
        Flypitch.Erdos1220.Sem.homog0 (cdot x block μ hμ) H)) with hΔdef
  by_contra hne
  have hΔ : ⊥ < Δ := bot_lt_iff_ne_bot.mpr (fun h => hne h.le)
  have h2μ : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hθ : ℵ₀ ≤ θ := h2μ.trans (Order.le_succ _)
  have hμθ : μ < θ := (cantor μ).trans_le (Order.le_succ _)
  have hI2 : #I ≤ 2 ^ μ := hI.trans (cantor μ).le
  have hxinf : ℵ₀ ≤ #x.Type := hθ.trans hθx.le
  have : Nonempty x.Type := Cardinal.mk_ne_zero_iff.mp (aleph0_pos.trans_le hxinf).ne'
  have : Nonempty I := ⟨block (Classical.arbitrary x.Type)⟩
  have hΔsub : Δ ≤ Flypitch.Erdos1220.Sem.subset H (check x) := inf_le_right.trans inf_le_left
  have hΔleq : Δ ≤ CardB.leqB (check x) H :=
    inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hΔhom : Δ ≤ Flypitch.Erdos1220.Sem.homog0 (cdot x block μ hμ) H :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  rcases two_large_or_pinned (x := x) (block := block) (hμ := hμ) hI hθ H hΔ with
    ⟨Δ', hpos, hle, b₁, b₂, hne12, hL1, hL2⟩ | ⟨q, hqΔ, b₀, Z, hZ, hkill⟩
  · -- (ii)
    obtain ⟨r, a, b, ha, hb, har, hbr, hblue, hr⟩ :=
      blue_pair_of_two_large hI2 H hpos hne12 hL1 hL2
    have hrΔ : emb r ≤ Δ := (hr.trans inf_le_left).trans hle
    have haH : emb r ≤ (check (x.Func a) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H :=
      hr.trans (inf_le_right.trans inf_le_left)
    have hbH : emb r ≤ (check (x.Func b) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H :=
      hr.trans (inf_le_right.trans inf_le_right)
    have hzero : emb r ≤ Flypitch.Erdos1220.Sem.zero (blueName x block μ hμ) := by
      rcases lt_or_gt_of_ne hne12 with hlt | hgt
      · have hab : x.Func a ∈ x.Func b := hord a b (ha ▸ hb ▸ hlt)
        exact homog0_kill _ H _ _ _ (check_mem hab) (hrΔ.trans hΔhom) haH hbH
          (emb_le_app_blue hab har hbr hblue)
      · have hba : x.Func b ∈ x.Func a := hord b a (ha ▸ hb ▸ hgt)
        exact homog0_kill _ H _ _ _ (check_mem hba) (hrΔ.trans hΔhom) hbH haH
          (emb_le_app_blue hba hbr har (r.last.symmetric hblue))
    exact absurd (lt_of_lt_of_le (emb_pos r) (blueName_eq_empty_le_bot hzero)) (lt_irrefl _)
  · -- (i)
    let S : Set x.Type := (⋃ b, Z b) ∪ block ⁻¹' {b₀}
    have hS : ∀ v, v ∉ S → emb q ⊓ (check (x.Func v) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ H
        ≤ ⊥ := by
      intro v hv
      refine hkill v (fun h => hv (Or.inr h)) (fun h => hv (Or.inl (mem_iUnion.mpr ⟨_, h⟩)))
    have hU : #(⋃ b, Z b) < #x.Type := by
      refine (mk_iUnion_le _).trans_lt ?_
      refine lt_of_le_of_lt (mul_le_mul' hI (ciSup_le' fun b => (hZ b).le)) ?_
      rw [mul_eq_max hμ hθ, max_eq_right hμθ.le]
      exact hθx
    have hSx : #S < #x.Type :=
      (mk_union_le _ _).trans_lt (add_lt_of_lt hxinf hU (hblk b₀))
    have hfib := exists_large_fiber_of_small (S := S) (θ := θ)
      (mul_lt_of_lt hxinf hSx hθx)
    have hcc := chainCondition_CAlg (antichain_CHP (V := x.Type) (block := block) (hμ := hμ) hI2)
    exact pinned_contra hcc (fun i j hij h => hij (hx i j h)) H S hfib (emb_pos q) hS
      (hqΔ.trans hΔsub) (hqΔ.trans hΔleq)

end Model

end RedExclusion

end Erdos1220Full

#print axioms Erdos1220Full.RedExclusion.antichain_CHP
#print axioms Erdos1220Full.RedExclusion.two_large_or_pinned
#print axioms Erdos1220Full.RedExclusion.pinned_contra
#print axioms Erdos1220Full.RedExclusion.exists_fresh_seq
#print axioms Erdos1220Full.RedExclusion.blue_pair_of_two_large
#print axioms Erdos1220Full.RedExclusion.red_exclusion
