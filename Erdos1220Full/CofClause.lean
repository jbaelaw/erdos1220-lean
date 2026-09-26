import Erdos1220Full.CardPreserveSem

/-!
# The cofinality clause of the hypotheses of #1220 in `V 𝔹`

For `l = check (ordinalMk lo)` we prove `⊤ ≤ ⨅ d, cof l d ⟹ omegaInacc d` from:

* `ν`-distributivity (`DistribHyp ν 𝔹`) and every `ρ < κ` satisfying
  `ρ.card ≤ ν` and `ρ.card < cof lo`;
* `κ̌ := check (card_ex κ)` is a cardinal and `ℵ₀`-inaccessible in `V 𝔹`;
* a cofinal `S₀ ⊆ l` with `|S₀| = |κ̌|` in `V 𝔹`.

The full identification `d = κ̌` is avoided. From `cof l d`: every cofinal
subset dominates `d`, so `|d| ≤ |κ̌|`; the cofinal subset of size `|d|`
excludes `d ∈ κ̌` by distributivity; hence `κ̌ ⊆ d`, and every cardinal
`μ' ∈ d` lies in `κ̌`, where the `ℵ₀`-inaccessibility of `κ̌` applies.
-/

open Cardinal Set Flypitch bSet Lattice

universe u

namespace Erdos1220Full.CardB

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-! ### Remaining predicates of `Statement1220.lean` -/

/-- `|A| = |B|` (`eqCardF`). -/
def eqCardB (A B : bSet 𝔹) : 𝔹 := leqB A B ⊓ leqB B A

/-- `d = cf(l)` (`cofF`). -/
def cofB (l d : bSet 𝔹) : 𝔹 :=
  cardinalB d ⊓ ((⨆ S : bSet 𝔹, subsetB S l ⊓ (cofinalB S l ⊓ eqCardB S d)) ⊓
    ⨅ S : bSet 𝔹, subsetB S l ⟹ (cofinalB S l ⟹ leqB d S))

/-- `k` is `ℵ₀`-inaccessible (`omegaInaccF`). -/
def omegaInaccB (k : bSet 𝔹) : 𝔹 := ⨅ μ : bSet 𝔹, μ ∈ᴮ k ⟹ (cardinalB μ ⟹ powLtB μ k)

/-! ### Boolean-valued helpers -/

theorem bot_of_le_iSup {ι : Type*} {A : 𝔹} {P : ι → 𝔹} (h : A ≤ ⨆ i, P i)
    (H : ∀ i, A ⊓ P i ≤ ⊥) : A ≤ ⊥ :=
  le_trans (le_inf le_rfl h) (le_trans (le_of_eq (inf_iSup_eq _ _)) (iSup_le H))

theorem mem_check_le {x : PSet.{u}} {z : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ z ∈ᴮ check x) :
    Γ ≤ ⨆ i : (check x : bSet 𝔹).type, z =ᴮ check (x.Func (check_cast i)) := by
  rw [mem_unfold] at h
  simpa only [check_bval_top, top_inf_eq, check_func] using h

theorem injOnB_apply {A f a a' z : bSet 𝔹} {Γ : 𝔹} (hI : Γ ≤ injOnB A f)
    (ha : Γ ≤ a ∈ᴮ A) (ha' : Γ ≤ a' ∈ᴮ A) (h1 : Γ ≤ appB f a z) (h2 : Γ ≤ appB f a' z) :
    Γ ≤ a =ᴮ a' := by
  have a1 := le_trans (le_inf (hI.trans (iInf_le _ a)) ha) bv_imp_elim
  have a2 := le_trans (le_inf (a1.trans (iInf_le _ a')) ha') bv_imp_elim
  have a3 := le_trans (le_inf (a2.trans (iInf_le _ z)) h1) bv_imp_elim
  exact le_trans (le_inf a3 h2) bv_imp_elim

/-- A `leqF`-witness restricted to `A × B` is a Flypitch injection. -/
theorem leqB_body_le_injects (A B f : bSet 𝔹) :
    isFunB A B f ⊓ injOnB A f ≤ injects_into A B := by
  set Γ := isFunB A B f ⊓ injOnB A f with hΓ
  refine le_iSup_of_le (f ∩ᴮ prod A B) (le_inf (le_inf ?_ ?_) ?_)
  · refine le_iInf fun w₁ => le_iInf fun w₂ => le_iInf fun v₁ => le_iInf fun v₂ => ?_
    rw [← deduction, ← deduction]
    set Γ' := Γ ⊓ (pair w₁ v₁ ∈ᴮ (f ∩ᴮ prod A B) ⊓ pair w₂ v₂ ∈ᴮ (f ∩ᴮ prod A B)) ⊓ w₁ =ᴮ w₂
    have m1 := mem_binary_inter_iff.mp
      (inf_le_left.trans (inf_le_right.trans inf_le_left) : Γ' ≤ pair w₁ v₁ ∈ᴮ (f ∩ᴮ prod A B))
    have m2 := mem_binary_inter_iff.mp
      (inf_le_left.trans (inf_le_right.trans inf_le_right) : Γ' ≤ pair w₂ v₂ ∈ᴮ (f ∩ᴮ prod A B))
    have hw₁ : Γ' ≤ w₁ ∈ᴮ A := (mem_prod_iff.mp m1.2).1
    have h2' : Γ' ≤ pair w₁ v₂ ∈ᴮ f :=
      bv_rw' (inf_le_right : Γ' ≤ w₁ =ᴮ w₂) (ϕ := fun w => pair w v₂ ∈ᴮ f)
        (h_congr := B_ext_pair_mem_left) (H_new := m2.1)
    exact isFunB_unique ((inf_le_left.trans inf_le_left).trans inf_le_left) hw₁ m1.1 h2'
  · refine le_iInf fun w₁ => ?_
    rw [← deduction]
    have h := le_trans (le_inf ((inf_le_left.trans inf_le_left : Γ ⊓ w₁ ∈ᴮ A ≤ isFunB A B f).trans
      (iInf_le _ w₁)) inf_le_right) bv_imp_elim
    refine le_trans (le_inf le_rfl h) (le_trans (le_of_eq (inf_iSup_eq _ _))
      (iSup_mono fun y => ?_))
    refine le_inf (inf_le_right.trans inf_le_left) (mem_binary_inter_iff.mpr
      ⟨inf_le_right.trans (inf_le_right.trans inf_le_left),
        prod_mem (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_left)⟩)
  · refine le_iInf fun w₁ => le_iInf fun w₂ => le_iInf fun v₁ => le_iInf fun v₂ => ?_
    rw [← deduction]
    set Γ' := Γ ⊓ (pair w₁ v₁ ∈ᴮ (f ∩ᴮ prod A B) ⊓ pair w₂ v₂ ∈ᴮ (f ∩ᴮ prod A B) ⊓ v₁ =ᴮ v₂)
    have m1 := mem_binary_inter_iff.mp
      (inf_le_right.trans (inf_le_left.trans inf_le_left) : Γ' ≤ pair w₁ v₁ ∈ᴮ (f ∩ᴮ prod A B))
    have m2 := mem_binary_inter_iff.mp
      (inf_le_right.trans (inf_le_left.trans inf_le_right) : Γ' ≤ pair w₂ v₂ ∈ᴮ (f ∩ᴮ prod A B))
    have hv : Γ' ≤ v₁ =ᴮ v₂ := inf_le_right.trans inf_le_right
    have h2' : Γ' ≤ pair w₂ v₁ ∈ᴮ f :=
      bv_rw' hv (ϕ := fun v => pair w₂ v ∈ᴮ f) (h_congr := B_ext_pair_mem_right) (H_new := m2.1)
    exact injOnB_apply (inf_le_left.trans inf_le_right) (mem_prod_iff.mp m1.2).1
      (mem_prod_iff.mp m2.2).1 m1.1 h2'

theorem leqB_le_injects_into (A B : bSet 𝔹) : leqB A B ≤ injects_into A B :=
  iSup_le fun f => leqB_body_le_injects A B f

/-- Transitivity of `|·| ≤ |·|` in `V 𝔹`. -/
theorem leqB_trans {A B C : bSet 𝔹} {Γ : 𝔹} (h₁ : Γ ≤ leqB A B) (h₂ : Γ ≤ leqB B C) :
    Γ ≤ leqB A C :=
  (injects_into_trans (h₁.trans (leqB_le_injects_into _ _))
    (h₂.trans (leqB_le_injects_into _ _))).trans (injects_into_le_leqB _ _)

/-- Enlarging the codomain. -/
theorem leqB_mono_right {A B B' : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ leqB A B) (hsub : Γ ≤ B ⊆ᴮ B') :
    Γ ≤ leqB A B' := by
  unfold leqB at h ⊢
  refine le_trans (le_inf le_rfl h) (le_trans (le_of_eq (inf_iSup_eq _ _)) (iSup_mono fun f => ?_))
  refine le_inf ?_ (inf_le_right.trans inf_le_right)
  unfold isFunB
  refine le_iInf fun x => ?_
  rw [← deduction]
  have hfun : Γ ⊓ (isFunB A B f ⊓ injOnB A f) ⊓ x ∈ᴮ A ≤ isFunB A B f :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have h1 : Γ ⊓ (isFunB A B f ⊓ injOnB A f) ⊓ x ∈ᴮ A ≤
      ⨆ y, y ∈ᴮ B ⊓ (appB f x y ⊓ ⨅ y', (appB f x y') ⟹ (y' =ᴮ y)) :=
    le_trans (le_inf (hfun.trans (iInf_le _ x)) inf_le_right) bv_imp_elim
  refine le_trans (le_inf le_rfl h1) (le_trans (le_of_eq (inf_iSup_eq _ _))
    (iSup_mono fun y => ?_))
  exact le_inf (mem_of_mem_subset (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hsub)))
    (inf_le_right.trans inf_le_left)) (inf_le_right.trans inf_le_right)

/-- Enlarging the bounding cardinal in `powLtF`. -/
theorem powLtB_mono {μ k k' : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ powLtB μ k) (hsub : Γ ≤ k ⊆ᴮ k') :
    Γ ≤ powLtB μ k' := by
  unfold powLtB at h ⊢
  refine le_trans (le_inf le_rfl h) (le_trans (le_of_eq (inf_iSup_eq _ _))
    (iSup_mono fun α => ?_))
  exact le_inf (mem_of_mem_subset (inf_le_left.trans hsub) (inf_le_right.trans inf_le_left))
    (inf_le_right.trans inf_le_right)

/-! ### No cofinal subset injects into a small ordinal -/

/-- **Key lemma.** Under `ν`-distributivity, no cofinal subset of a ground
ordinal `lo` injects into a ground ordinal `ρ` with `ρ.card ≤ ν` and
`ρ.card < cof lo`. -/
theorem cofSmall_eq_bot {ν : Cardinal.{u}} (hd : DistribHyp ν 𝔹) {ρ lo : Ordinal.{u}}
    (hρν : ρ.card ≤ ν) (hρcof : ρ.card < lo.cof) :
    (⨆ S : bSet 𝔹, subsetB S (check (PSet.ordinalMk lo)) ⊓
      (cofinalB S (check (PSet.ordinalMk lo)) ⊓ leqB S (check (PSet.ordinalMk ρ))) : 𝔹) = ⊥ := by
  classical
  have hlo0 : (0 : Ordinal) < lo := by
    rcases eq_or_ne lo 0 with h' | h'
    · rw [h', Ordinal.cof_zero] at hρcof
      exact absurd hρcof (by simp)
    · exact pos_iff_ne_zero.mpr h'
  set x := PSet.ordinalMk ρ with hx
  set y := PSet.ordinalMk lo with hy
  apply le_bot_iff.mp
  apply poset_yoneda
  intro Γ hΓ
  by_cases h0 : Γ = ⊥
  · exact h0.le
  have hpos : ⊥ < Γ := bot_lt_iff_ne_bot.mpr h0
  obtain ⟨S, hS⟩ := nonzero_wit' hpos hΓ
  set Γ₀ := subsetB S (check y) ⊓ (cofinalB S (check y) ⊓ leqB S (check x)) with hΓ₀
  have hpos0 : ⊥ < Γ₀ := lt_of_lt_of_le hS inf_le_left
  obtain ⟨h, hh⟩ := nonzero_wit' hpos0
    (show Γ₀ ≤ ⨆ h, isFunB S (check x) h ⊓ injOnB S h from inf_le_right.trans inf_le_right)
  set Γ₁ := isFunB S (check x) h ⊓ injOnB S h ⊓ Γ₀ with hΓ₁
  have hsub : Γ₁ ≤ subsetB S (check y) := inf_le_right.trans inf_le_left
  have hcof : Γ₁ ≤ cofinalB S (check y) := inf_le_right.trans (inf_le_right.trans inf_le_left)
  have hF : Γ₁ ≤ isFunB S (check x) h := inf_le_left.trans inf_le_left
  have hI : Γ₁ ≤ injOnB S h := inf_le_left.trans inf_le_right
  set T : x.Type → 𝔹 := fun γ => ⨆ β : y.Type,
    (check (y.Func β) : bSet 𝔹) ∈ᴮ S ⊓ appB h (check (y.Func β)) (check (x.Func γ)) with hT
  set φ : ∀ γ : x.Type, Option y.Type → 𝔹 := fun γ o => Option.elim o (T γ)ᶜ
    (fun β => (check (y.Func β) : bSet 𝔹) ∈ᴮ S ⊓ appB h (check (y.Func β)) (check (x.Func γ)))
    with hφ
  have hxcard : #x.Type = ρ.card := PSet.ordinalMk_card
  obtain ⟨Δ, hΔpos, hΔle, c, hc⟩ := hd x.Type (hxcard ▸ hρν) (fun _ => Option y.Type) φ Γ₁ hh
    (fun γ => le_trans (bv_em (T γ)) (sup_le
      (iSup_le fun β => le_iSup_of_le (some β) le_rfl) (le_iSup_of_le none le_rfl)))
  choose ordOf hordlt hordeq using
    fun β : y.Type => PSet.mem_ordinalMk_iff.mp (PSet.func_mem y β)
  set v : x.Type → Ordinal.{u} := fun γ => Option.elim (c γ) 0 ordOf with hvdef
  have hv : ∀ γ, v γ < lo := by
    intro γ
    rcases hco : c γ with _ | β
    · simp only [v, hco, Option.elim]; exact hlo0
    · simp only [v, hco, Option.elim]; exact hordlt β
  obtain ⟨σ, hσ, hσbound⟩ := exists_strict_bound (J := x.Type) (hxcard ▸ hρcof) v hv
  obtain ⟨β₀, hβ₀⟩ := PSet.mem_unfold.mp (PSet.mk_mem_mk_of_lt hσ)
  have hordβ₀ : σ = ordOf β₀ := PSet.eq_of_mk_equiv (hβ₀.trans (hordeq β₀))
  set b : bSet 𝔹 := check (y.Func β₀) with hbdef
  have hground : ∀ β'', ordOf β'' < ordOf β₀ →
      (b ∈ᴮ check (y.Func β'') ⊔ b =ᴮ check (y.Func β'') : 𝔹) ≤ ⊥ := by
    intro β'' hlt
    have hnm : ¬ (y.Func β₀ ∈ y.Func β'') := by
      intro hmem
      have h1 := (PSet.Mem.congr_left (hordeq β₀)).mp hmem
      have h2 := (PSet.Mem.congr_right (hordeq β'')).mp h1
      exact absurd (PSet.ordinalMk_lt_of_mem h2) (not_lt.mpr hlt.le)
    have hne : ¬ PSet.Equiv (y.Func β₀) (y.Func β'') := by
      intro heqv
      have := PSet.eq_of_mk_equiv ((hordeq β₀).symm.trans (heqv.trans (hordeq β'')))
      exact absurd this (ne_of_gt hlt)
    exact sup_le (check_not_mem hnm le_rfl) (le_of_eq (check_bv_eq_bot_of_not_equiv hne))
  have hb : Δ ≤ ⨆ g, g ∈ᴮ S ⊓ (b ∈ᴮ g ⊔ b =ᴮ g) :=
    le_trans (le_inf ((hΔle.trans hcof).trans (iInf_le _ b)) mem_check_of_mem) bv_imp_elim
  have hbot : Δ ≤ ⊥ := by
    refine bot_of_le_iSup hb fun g => ?_
    set Δ₁ := Δ ⊓ (g ∈ᴮ S ⊓ (b ∈ᴮ g ⊔ b =ᴮ g)) with hΔ₁
    have hgS : Δ₁ ≤ g ∈ᴮ S := inf_le_right.trans inf_le_left
    have hSy : Δ₁ ≤ S ⊆ᴮ check y := by
      rw [← subsetB_eq]; exact (inf_le_left.trans hΔle).trans hsub
    have hgy : Δ₁ ≤ g ∈ᴮ check y := mem_of_mem_subset hSy hgS
    refine bot_of_le_iSup (mem_check_le hgy) fun i => ?_
    set β := check_cast i with hβ
    set e : bSet 𝔹 := check (y.Func β) with he
    set Δ₂ := Δ₁ ⊓ g =ᴮ e with hΔ₂
    have heq : Δ₂ ≤ g =ᴮ e := inf_le_right
    have heS : Δ₂ ≤ e ∈ᴮ S :=
      bv_rw' (bv_symm heq) (ϕ := fun w => w ∈ᴮ S) (h_congr := B_ext_mem_left)
        (H_new := inf_le_left.trans hgS)
    have heb : Δ₂ ≤ b ∈ᴮ e ⊔ b =ᴮ e :=
      bv_rw' (bv_symm heq) (ϕ := fun w => b ∈ᴮ w ⊔ b =ᴮ w)
        (h_congr := B_ext_sup (h₁ := B_ext_mem_right) (h₂ := B_ext_bv_eq_right))
        (H_new := inf_le_left.trans (inf_le_right.trans inf_le_right))
    have hΔ₂Δ : Δ₂ ≤ Δ := inf_le_left.trans inf_le_left
    have hval : Δ₂ ≤ ⨆ z, z ∈ᴮ (check x : bSet 𝔹) ⊓
        (appB h e z ⊓ ⨅ y', (appB h e y') ⟹ (y' =ᴮ z)) :=
      le_trans (le_inf (((hΔ₂Δ.trans hΔle).trans hF).trans (iInf_le _ e)) heS) bv_imp_elim
    refine bot_of_le_iSup hval fun z => ?_
    set Δ₃ := Δ₂ ⊓ (z ∈ᴮ (check x : bSet 𝔹) ⊓ (appB h e z ⊓ ⨅ y', (appB h e y') ⟹ (y' =ᴮ z)))
      with hΔ₃
    refine bot_of_le_iSup (mem_check_le (inf_le_right.trans inf_le_left : Δ₃ ≤ z ∈ᴮ check x))
      fun j => ?_
    set γ := check_cast j with hγ
    set Δ₄ := Δ₃ ⊓ z =ᴮ check (x.Func γ) with hΔ₄
    have happ : Δ₄ ≤ appB h e (check (x.Func γ)) :=
      bv_rw' (bv_symm inf_le_right) (ϕ := fun w => appB h e w) (h_congr := B_ext_pair_mem_right)
        (H_new := inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    have hΔ₄Δ : Δ₄ ≤ Δ := inf_le_left.trans (inf_le_left.trans hΔ₂Δ)
    have heS₄ : Δ₄ ≤ e ∈ᴮ S := inf_le_left.trans (inf_le_left.trans heS)
    have heb₄ : Δ₄ ≤ b ∈ᴮ e ⊔ b =ᴮ e := inf_le_left.trans (inf_le_left.trans heb)
    have hcγ := hc γ
    cases hco : c γ with
    | none =>
      rw [hco] at hcγ
      have hT' : Δ₄ ≤ T γ := le_iSup_of_le β (le_inf heS₄ happ)
      calc Δ₄ ≤ (T γ)ᶜ ⊓ T γ := le_inf (hΔ₄Δ.trans hcγ) hT'
        _ = ⊥ := compl_inf_self _
    | some β'' =>
      rw [hco] at hcγ
      have hlt : ordOf β'' < ordOf β₀ := by
        have := hσbound γ
        simp only [v, hco, Option.elim] at this
        rw [← hordβ₀]; exact this
      have hee : Δ₄ ≤ e =ᴮ check (y.Func β'') :=
        injOnB_apply ((hΔ₄Δ.trans hΔle).trans hI) heS₄ ((hΔ₄Δ.trans hcγ).trans inf_le_left)
          happ ((hΔ₄Δ.trans hcγ).trans inf_le_right)
      have hb'' : Δ₄ ≤ b ∈ᴮ check (y.Func β'') ⊔ b =ᴮ check (y.Func β'') :=
        bv_rw' (bv_symm hee) (ϕ := fun w => b ∈ᴮ w ⊔ b =ᴮ w)
          (h_congr := B_ext_sup (h₁ := B_ext_mem_right) (h₂ := B_ext_bv_eq_right))
          (H_new := heb₄)
      exact hb''.trans (hground β'' hlt)
  exact absurd (lt_of_lt_of_le hΔpos hbot) (lt_irrefl _)

/-- A cofinal subset of `l` of the same size as `d` excludes `d ∈ κ̌`. -/
theorem not_mem_of_cof {ν : Cardinal.{u}} (hd : DistribHyp ν 𝔹) {κ : Cardinal.{u}}
    {lo : Ordinal.{u}} (hsmall : ∀ ρ < κ.ord, ρ.card ≤ ν ∧ ρ.card < lo.cof) (d : bSet 𝔹) :
    (⨆ S : bSet 𝔹, subsetB S (check (PSet.ordinalMk lo)) ⊓
      (cofinalB S (check (PSet.ordinalMk lo)) ⊓ eqCardB S d)) ⊓
      d ∈ᴮ (check (PSet.card_ex κ) : bSet 𝔹) ≤ ⊥ := by
  set L : bSet 𝔹 := check (PSet.ordinalMk lo) with hL
  let W : bSet 𝔹 → 𝔹 := fun d => ⨆ S : bSet 𝔹, subsetB S L ⊓ (cofinalB S L ⊓ leqB S d)
  have hW : B_ext W := B_ext_iSup (h := fun S => B_ext_inf B_ext_const
    (B_ext_inf B_ext_const (B_ext_leqB_right S)))
  have hstep : (⨆ S : bSet 𝔹, subsetB S L ⊓ (cofinalB S L ⊓ eqCardB S d)) ≤ W d :=
    iSup_mono fun S => inf_le_inf_left _ (inf_le_inf_left _ inf_le_left)
  refine le_trans (inf_le_inf_right _ hstep) ?_
  refine bot_of_le_iSup (mem_check_le (inf_le_right : W d ⊓ d ∈ᴮ _ ≤ _)) fun i => ?_
  obtain ⟨ρ, hρ, hequiv⟩ := card_ex_func_equiv κ (check_cast i)
  have h1 : (W d ⊓ d ∈ᴮ (check (PSet.card_ex κ) : bSet 𝔹)) ⊓
      d =ᴮ check ((PSet.card_ex κ).Func (check_cast i)) ≤
      W (check ((PSet.card_ex κ).Func (check_cast i))) :=
    le_trans (le_inf inf_le_right (inf_le_left.trans inf_le_left)) (hW _ _)
  have h2 : W (check ((PSet.card_ex κ).Func (check_cast i))) ≤ W (check (PSet.ordinalMk ρ)) :=
    le_trans (le_inf (check_bv_eq hequiv) le_rfl) (hW _ _)
  have h3 : W (check (PSet.ordinalMk ρ)) = ⊥ :=
    cofSmall_eq_bot hd (hsmall ρ hρ).1 (hsmall ρ hρ).2
  exact (h1.trans h2).trans (le_of_eq h3)

/-- **The cofinality clause.** -/
theorem cof_clause {ν : Cardinal.{u}} (hd : DistribHyp ν 𝔹) {κ : Cardinal.{u}}
    {lo : Ordinal.{u}} (hsmall : ∀ ρ < κ.ord, ρ.card ≤ ν ∧ ρ.card < lo.cof)
    (hκcard : (⊤ : 𝔹) ≤ cardinalB (check (PSet.card_ex κ)))
    (hκinacc : (⊤ : 𝔹) ≤ omegaInaccB (check (PSet.card_ex κ)))
    (S₀ : bSet 𝔹) (hS₀sub : (⊤ : 𝔹) ≤ subsetB S₀ (check (PSet.ordinalMk lo)))
    (hS₀cof : (⊤ : 𝔹) ≤ cofinalB S₀ (check (PSet.ordinalMk lo)))
    (hS₀eq : (⊤ : 𝔹) ≤ eqCardB S₀ (check (PSet.card_ex κ))) :
    (⊤ : 𝔹) ≤ ⨅ d : bSet 𝔹, cofB (check (PSet.ordinalMk lo)) d ⟹ omegaInaccB d := by
  set L : bSet 𝔹 := check (PSet.ordinalMk lo) with hL
  set K : bSet 𝔹 := check (PSet.card_ex κ) with hK
  refine le_iInf fun d => ?_
  rw [← deduction]
  set Γ := (⊤ : 𝔹) ⊓ cofB L d with hΓ
  have hcof : Γ ≤ cofB L d := inf_le_right
  have hcardd : Γ ≤ cardinalB d := hcof.trans inf_le_left
  have hW : Γ ≤ ⨆ S : bSet 𝔹, subsetB S L ⊓ (cofinalB S L ⊓ eqCardB S d) :=
    hcof.trans (inf_le_right.trans inf_le_left)
  have hdom : Γ ≤ ⨅ S : bSet 𝔹, subsetB S L ⟹ (cofinalB S L ⟹ leqB d S) :=
    hcof.trans (inf_le_right.trans inf_le_right)
  have hdS : Γ ≤ leqB d S₀ :=
    le_trans (le_inf (le_trans (le_inf (hdom.trans (iInf_le _ S₀)) (le_top.trans hS₀sub))
      bv_imp_elim) (le_top.trans hS₀cof)) bv_imp_elim
  have hdK : Γ ≤ leqB d K := leqB_trans hdS (le_top.trans (hS₀eq.trans inf_le_left))
  have hnot : Γ ⊓ d ∈ᴮ K ≤ ⊥ :=
    le_trans (inf_le_inf_right _ hW) (not_mem_of_cof hd hsmall d)
  have hOrdd : Γ ≤ bSet.Ord d := by rw [← ordB_eq_Ord]; exact hcardd.trans inf_le_left
  have hOrdK : ∀ {Γ' : 𝔹}, Γ' ≤ bSet.Ord K := fun {Γ'} => Ord_card_ex κ
  have hKd : Γ ≤ K ⊆ᴮ d := by
    have htri := Ord.trichotomy hOrdd hOrdK
    refine le_trans (le_inf le_rfl htri) ?_
    rw [inf_sup_left, inf_sup_left]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact subset_of_eq (bv_symm inf_le_right)
    · exact le_trans hnot bot_le
    · exact subset_of_mem_transitive ((inf_le_left.trans hOrdd).trans inf_le_right) inf_le_right
  refine le_iInf fun μ' => ?_
  rw [← deduction, ← deduction]
  set Γ' := Γ ⊓ μ' ∈ᴮ d ⊓ cardinalB μ' with hΓ'def
  have hΓ' : Γ' ≤ Γ := inf_le_left.trans inf_le_left
  have hμd : Γ' ≤ μ' ∈ᴮ d := inf_le_left.trans inf_le_right
  have hμcard : Γ' ≤ cardinalB μ' := inf_le_right
  have hOrdμ : Γ' ≤ bSet.Ord μ' := by rw [← ordB_eq_Ord]; exact hμcard.trans inf_le_left
  have hnotleq : Γ' ⊓ leqB d μ' ≤ ⊥ := by
    have h1 : Γ' ≤ (leqB d μ')ᶜ :=
      le_trans (le_inf (((hΓ'.trans hcardd).trans inf_le_right).trans (iInf_le _ μ')) hμd)
        bv_imp_elim
    calc Γ' ⊓ leqB d μ' ≤ (leqB d μ')ᶜ ⊓ leqB d μ' := inf_le_inf_right _ h1
      _ = ⊥ := compl_inf_self _
  have hμK : Γ' ≤ μ' ∈ᴮ K := by
    have htri := Ord.trichotomy hOrdμ (hOrdK (Γ' := Γ'))
    refine le_trans (le_inf le_rfl htri) ?_
    rw [inf_sup_left, inf_sup_left]
    refine sup_le (sup_le ?_ inf_le_right) ?_
    · refine le_trans (le_trans (le_inf inf_le_left ?_) hnotleq) bot_le
      exact leqB_congr_right d (bv_symm inf_le_right) ((inf_le_left.trans hΓ').trans hdK)
    · refine le_trans (le_trans (le_inf inf_le_left ?_) hnotleq) bot_le
      exact leqB_mono_right ((inf_le_left.trans hΓ').trans hdK)
        (subset_of_mem_transitive ((inf_le_left.trans hOrdμ).trans inf_le_right) inf_le_right)
  have hpowK : Γ' ≤ powLtB μ' K :=
    le_trans (le_inf (le_trans (le_inf ((le_top.trans hκinacc).trans (iInf_le _ μ')) hμK)
      bv_imp_elim) hμcard) bv_imp_elim
  exact powLtB_mono hpowK (hΓ'.trans hKd)

/-! ### Restatement for `Semantics1220` -/

section Sem

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

theorem sem_eqCard_eq (A B : bSet β) : Flypitch.Erdos1220.Sem.eqCard A B = eqCardB A B := rfl

theorem sem_cof_eq (l d : bSet β) : Flypitch.Erdos1220.Sem.cof l d = cofB l d := rfl

theorem sem_omegaInacc_eq (k : bSet β) :
    Flypitch.Erdos1220.Sem.omegaInacc k = omegaInaccB k := rfl

/-- **The cofinality clause of `Sem.hyp`.** -/
theorem sem_cof_clause {ν : Cardinal.{0}} (hd : DistribHyp ν β) {κ : Cardinal.{0}}
    {lo : Ordinal.{0}} (hsmall : ∀ ρ < κ.ord, ρ.card ≤ ν ∧ ρ.card < lo.cof)
    (hκcard : (⊤ : β) ≤ Flypitch.Erdos1220.Sem.cardinal (check (PSet.card_ex κ)))
    (hκinacc : (⊤ : β) ≤ Flypitch.Erdos1220.Sem.omegaInacc (check (PSet.card_ex κ)))
    (S₀ : bSet β)
    (hS₀sub : (⊤ : β) ≤ Flypitch.Erdos1220.Sem.subset S₀ (check (PSet.ordinalMk lo)))
    (hS₀cof : (⊤ : β) ≤ Flypitch.Erdos1220.Sem.cofinal S₀ (check (PSet.ordinalMk lo)))
    (hS₀eq : (⊤ : β) ≤ Flypitch.Erdos1220.Sem.eqCard S₀ (check (PSet.card_ex κ))) :
    (⊤ : β) ≤ ⨅ d : bSet β, Flypitch.Erdos1220.Sem.cof (check (PSet.ordinalMk lo)) d ⟹
      Flypitch.Erdos1220.Sem.omegaInacc d :=
  cof_clause hd hsmall hκcard hκinacc S₀ hS₀sub hS₀cof hS₀eq

end Sem

end Erdos1220Full.CardB

#print axioms Erdos1220Full.CardB.leqB_trans
#print axioms Erdos1220Full.CardB.cofSmall_eq_bot
#print axioms Erdos1220Full.CardB.not_mem_of_cof
#print axioms Erdos1220Full.CardB.cof_clause
#print axioms Erdos1220Full.CardB.sem_cof_clause
