import Erdos1220Full.CoverForcing
import Erdos1220Full.Semantics1220

/-!
# The generic colouring name

Universe `0`. The vertex set is `x.Type` for a ground pre-set `x`
(think of an ordinal: elements pairwise non-equivalent, `∈` the order), with a
block map `block : x.Type → I`; the forcing is the covering historical forcing
`CHP0` and `𝔹 = CAlg x.Type I block μ hμ : Type`.

* colour `true` = blue = `1`, named by `blueName = {∅}`;
  colour `false` = red = `0`, named by `∅`;
* `Decides q a b c`: both vertices are in the terminal support of `q` and
  `q.last.blue a b ↔ c = true`;
* `cdot` has members `((ǎ, b̌), colour)` for `x.Func a ∈ x.Func b`, with
  Boolean value `colVal a b c = ⨆ {q // Decides q a b c}, emb q`.

Main results: `colouring_cdot : ⊤ ≤ Sem.colouring (check x) cdot` and the
decision lemmas `exists_blue_of_app_one`, `exists_red_of_app_zero`.
-/

open Cardinal Set Order Flypitch bSet Lattice

namespace Erdos1220Full

namespace GenericColouring

open Erdos1220 Erdos1220.BasicCondition HistoryForcing
open Flypitch.Erdos1220

section Defs

variable {I : Type} (x : PSet.{0}) (block : x.Type → I) (μ : Cardinal.{0}) (hμ : ℵ₀ ≤ μ)

/-- `q` decides the colour of `(a, b)` to be `c` (`true` = blue). -/
def Decides (q : CHP0 x.Type I block μ hμ) (a b : x.Type) (c : Bool) : Prop :=
  a ∈ q.last.support ∧ b ∈ q.last.support ∧ (q.last.blue a b ↔ c = true)

variable [Nonempty (CHP0 x.Type I block μ hμ)]

/-- The name `{∅}` of colour `1` (blue). -/
noncomputable def blueName : bSet (CAlg x.Type I block μ hμ) :=
  bSet.mk PUnit (fun _ => bSet.empty) (fun _ => ⊤)

/-- The name of a colour. -/
noncomputable def colourName : Bool → bSet (CAlg x.Type I block μ hμ)
  | true => blueName x block μ hμ
  | false => bSet.empty

/-- The Boolean value of "the pair `(a, b)` has colour `c`". -/
noncomputable def colVal (a b : x.Type) (c : Bool) : CAlg x.Type I block μ hμ :=
  ⨆ q : {q : CHP0 x.Type I block μ hμ // Decides x block μ hμ q a b c}, emb q.1

/-- The generic colouring. -/
noncomputable def cdot : bSet (CAlg x.Type I block μ hμ) :=
  bSet.mk {t : x.Type × x.Type × Bool // x.Func t.1 ∈ x.Func t.2.1}
    (fun t => pair (pair (check (x.Func t.1.1)) (check (x.Func t.1.2.1)))
      (colourName x block μ hμ t.1.2.2))
    (fun t => colVal x block μ hμ t.1.1 t.1.2.1 t.1.2.2)

end Defs

variable {I : Type} {x : PSet.{0}} {block : x.Type → I} {μ : Cardinal.{0}} {hμ : ℵ₀ ≤ μ}

/-! ## Order-theoretic facts about deciding -/

theorem Decides.mono {q r : CHP0 x.Type I block μ hμ} {a b : x.Type} {c : Bool}
    (hq : Decides x block μ hμ q a b c) (hrq : r ≤ q) : Decides x block μ hμ r a b c := by
  obtain ⟨ha, hb, hc⟩ := hq
  have hext := CHP0.last_extends hrq
  exact ⟨hext.1 ha, hext.1 hb, ((hext.2 a ha b hb).trans hc)⟩

theorem exists_le_decides (q : CHP0 x.Type I block μ hμ) (a b : x.Type) :
    ∃ r, r ≤ q ∧ ∃ c, Decides x block μ hμ r a b c := by
  classical
  obtain ⟨r₁, hr₁, ha⟩ := q.exists_le_mem a
  obtain ⟨r₂, hr₂, hb⟩ := r₁.exists_le_mem b
  have ha₂ : a ∈ r₂.last.support := (CHP0.last_extends hr₂).1 ha
  refine ⟨r₂, le_trans hr₂ hr₁, ?_⟩
  by_cases h : r₂.last.blue a b
  · exact ⟨true, ha₂, hb, by simp [h]⟩
  · exact ⟨false, ha₂, hb, by simp [h]⟩

theorem decides_unique {q q' : CHP0 x.Type I block μ hμ} {a b : x.Type} {c c' : Bool}
    (hq : Decides x block μ hμ q a b c) (hq' : Decides x block μ hμ q' a b c')
    (hcomp : Compatible q q') : c = c' := by
  obtain ⟨r, hrq, hrq'⟩ := hcomp
  have h₁ := (hq.mono hrq).2.2
  have h₂ := (hq'.mono hrq').2.2
  have h : c = true ↔ c' = true := h₁.symm.trans h₂
  cases c <;> cases c' <;> simp_all

variable [Nonempty (CHP0 x.Type I block μ hμ)]

omit [Nonempty (CHP0 x.Type I block μ hμ)] in
theorem emb_le_colVal {q : CHP0 x.Type I block μ hμ} {a b : x.Type} {c : Bool}
    (hq : Decides x block μ hμ q a b c) : emb q ≤ colVal x block μ hμ a b c :=
  le_iSup (fun q : {q : CHP0 x.Type I block μ hμ // Decides x block μ hμ q a b c} => emb q.1)
    ⟨q, hq⟩

theorem emb_inf_colVal_eq_bot {q : CHP0 x.Type I block μ hμ} {a b : x.Type} {c c' : Bool}
    (hq : Decides x block μ hμ q a b c) (hcc : c ≠ c') :
    emb q ⊓ colVal x block μ hμ a b c' = ⊥ := by
  rw [colVal, inf_iSup_eq]
  apply le_antisymm _ bot_le
  apply iSup_le
  rintro ⟨q', hq'⟩
  exact le_of_eq (emb_inf_eq_bot_of_not_compatible
    (fun hcomp => hcc (decides_unique hq hq' hcomp)))

theorem exists_emb_le_decides {Γ : CAlg x.Type I block μ hμ} (hΓ : ⊥ < Γ) (a b : x.Type) :
    ∃ q c, emb q ≤ Γ ∧ Decides x block μ hμ q a b c := by
  obtain ⟨p, hp⟩ := exists_emb_le hΓ
  obtain ⟨r, hr, c, hc⟩ := exists_le_decides p a b
  exact ⟨r, c, (emb_mono hr).trans hp, hc⟩

/-! ## The colour names -/

theorem mem_blueName (z : bSet (CAlg x.Type I block μ hμ)) :
    z ∈ᴮ blueName x block μ hμ = z =ᴮ bSet.empty := by
  rw [mem_unfold]
  show (⨆ _i : PUnit, (⊤ : CAlg x.Type I block μ hμ) ⊓ z =ᴮ bSet.empty) = _
  rw [iSup_const, top_inf_eq]

theorem one_blueName : (⊤ : CAlg x.Type I block μ hμ) ≤ Sem.one (blueName x block μ hμ) := by
  unfold Sem.one
  apply le_iInf
  intro z
  rw [mem_blueName, bihimp_eq, sup_compl_eq_top, inf_idem]

theorem zero_empty : (⊤ : CAlg x.Type I block μ hμ) ≤ Sem.zero bSet.empty :=
  bv_refl

theorem blueName_eq_empty_le_bot {Γ : CAlg x.Type I block μ hμ}
    (h : Γ ≤ blueName x block μ hμ =ᴮ bSet.empty) : Γ ≤ ⊥ := by
  have hmem : Γ ≤ (bSet.empty : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ blueName x block μ hμ := by
    rw [mem_blueName]; exact bv_refl
  have h' : Γ ≤ (bSet.empty : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ bSet.empty :=
    bv_rw' (bv_symm h) (ϕ := fun w => (bSet.empty : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ w)
      (h_congr := B_ext_mem_right) (H_new := hmem)
  exact bot_of_mem_empty h'

theorem mem_of_one {Γ : CAlg x.Type I block μ hμ} {i : bSet (CAlg x.Type I block μ hμ)}
    (h : Γ ≤ Sem.one i) : Γ ≤ (bSet.empty : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ i := by
  have h₁ : Γ ≤ bihimp ((bSet.empty : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ i)
      (bSet.empty =ᴮ bSet.empty) := h.trans (iInf_le _ bSet.empty)
  have he : ((bSet.empty : bSet (CAlg x.Type I block μ hμ)) =ᴮ bSet.empty) = ⊤ :=
    top_unique bv_refl
  rw [he, bihimp_eq, compl_top, sup_bot_eq] at h₁
  exact h₁.trans inf_le_left

/-! ## Membership in `cdot` -/

theorem inf_mem_cdot_le {E G : CAlg x.Type I block μ hμ} {z : bSet (CAlg x.Type I block μ hμ)}
    (h : ∀ (a' b' : x.Type) (c' : Bool), x.Func a' ∈ x.Func b' →
      E ⊓ (colVal x block μ hμ a' b' c' ⊓
        z =ᴮ pair (pair (check (x.Func a')) (check (x.Func b'))) (colourName x block μ hμ c'))
        ≤ G) :
    E ⊓ z ∈ᴮ cdot x block μ hμ ≤ G := by
  rw [mem_unfold, inf_iSup_eq]
  apply iSup_le
  rintro ⟨⟨a', b', c'⟩, hab⟩
  exact h a' b' c' hab

theorem le_mem_cdot {E : CAlg x.Type I block μ hμ} {z : bSet (CAlg x.Type I block μ hμ)}
    {a b : x.Type} {c : Bool} (hab : x.Func a ∈ x.Func b)
    (hv : E ≤ colVal x block μ hμ a b c)
    (hz : E ≤ z =ᴮ pair (pair (check (x.Func a)) (check (x.Func b))) (colourName x block μ hμ c)) :
    E ≤ z ∈ᴮ cdot x block μ hμ := by
  rw [mem_unfold]
  exact le_trans (le_inf hv hz)
    (le_iSup (fun t : {t : x.Type × x.Type × Bool // x.Func t.1 ∈ x.Func t.2.1} =>
      colVal x block μ hμ t.1.1 t.1.2.1 t.1.2.2 ⊓
        z =ᴮ pair (pair (check (x.Func t.1.1)) (check (x.Func t.1.2.1)))
          (colourName x block μ hμ t.1.2.2)) ⟨(a, b, c), hab⟩)

/-- Equal pairs of check vertices have equal coordinates, or the value is `⊥`. -/
theorem eq_pair_cases (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    {F : CAlg x.Type I block μ hμ} {a b a' b' : x.Type} {i n : bSet (CAlg x.Type I block μ hμ)}
    (hF : F ≤ pair (pair (check (x.Func a)) (check (x.Func b))) i =ᴮ
      pair (pair (check (x.Func a')) (check (x.Func b'))) n) :
    (a = a' ∧ b = b' ∧ F ≤ i =ᴮ n) ∨ F ≤ ⊥ := by
  obtain ⟨h₁, h₂⟩ := eq_of_eq_pair hF
  obtain ⟨ha, hb⟩ := eq_of_eq_pair h₁
  by_cases ea : a = a'
  · by_cases eb : b = b'
    · exact Or.inl ⟨ea, eb, h₂⟩
    · exact Or.inr (hb.trans (le_of_eq (check_bv_eq_bot_of_not_equiv
        (fun h => eb (hx _ _ h)))))
  · exact Or.inr (ha.trans (le_of_eq (check_bv_eq_bot_of_not_equiv
      (fun h => ea (hx _ _ h)))))

/-! ## `cdot` is forced to be a colouring of `check x` -/

theorem colouring_cdot (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j) :
    (⊤ : CAlg x.Type I block μ hμ) ≤ Sem.colouring (check x) (cdot x block μ hμ) := by
  unfold Sem.colouring
  apply le_iInf; intro A; rw [← deduction]
  apply le_iInf; intro B; rw [← deduction, ← deduction]
  apply le_of_positive_refinements
  intro Δ hΔ hΔle
  have hA : Δ ≤ A ∈ᴮ check x := hΔle.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hB : Δ ≤ B ∈ᴮ check x := hΔle.trans (inf_le_left.trans inf_le_right)
  have hAB : Δ ≤ A ∈ᴮ B := hΔle.trans inf_le_right
  obtain ⟨a, Δ₁, hΔ₁, hΔ₁le, hAa⟩ := eq_check_of_mem_check hΔ hA
  obtain ⟨b, Δ₂, hΔ₂, hΔ₂le, hBb⟩ := eq_check_of_mem_check hΔ₁ (hΔ₁le.trans hB)
  have hAa₂ : Δ₂ ≤ A =ᴮ check (x.Func a) := hΔ₂le.trans hAa
  have hmem₁ : Δ₂ ≤ check (x.Func a) ∈ᴮ B :=
    bv_rw' (bv_symm hAa₂) (ϕ := fun w => w ∈ᴮ B) (h_congr := B_ext_mem_left)
      (H_new := hΔ₂le.trans (hΔ₁le.trans hAB))
  have hmem₂ : Δ₂ ≤ check (x.Func a) ∈ᴮ check (x.Func b) :=
    bv_rw' (bv_symm hBb) (ϕ := fun w => check (x.Func a) ∈ᴮ w) (h_congr := B_ext_mem_right)
      (H_new := hmem₁)
  have hab : x.Func a ∈ x.Func b := by
    by_contra hn
    exact (not_le_of_gt hΔ₂) (check_not_mem hn hmem₂)
  obtain ⟨q, c, hqΔ, hqc⟩ := exists_emb_le_decides hΔ₂ a b
  refine ⟨emb q, emb_pos q, hqΔ.trans (hΔ₂le.trans hΔ₁le), ?_⟩
  have hqA : emb q ≤ A =ᴮ check (x.Func a) := hqΔ.trans hAa₂
  have hqB : emb q ≤ B =ᴮ check (x.Func b) := hqΔ.trans hBb
  have hpairAB : ∀ {E : CAlg x.Type I block μ hμ} (n : bSet (CAlg x.Type I block μ hμ)),
      E ≤ emb q → E ≤ pair (pair A B) n =ᴮ
        pair (pair (check (x.Func a)) (check (x.Func b))) n :=
    fun n hE => pair_congr (pair_congr (hE.trans hqA) (hE.trans hqB)) bv_refl
  apply bv_use (colourName x block μ hμ c)
  refine le_inf ?_ (le_inf ?_ ?_)
  · -- existence
    exact le_mem_cdot hab (emb_le_colVal hqc) (hpairAB _ le_rfl)
  · -- the value is a colour
    cases c
    · exact le_sup_of_le_left (le_top.trans zero_empty)
    · exact le_sup_of_le_right (le_top.trans one_blueName)
  · -- uniqueness
    apply le_iInf
    intro i'
    rw [← deduction]
    have hE : emb q ⊓ Flypitch.Erdos501.Sem.app (cdot x block μ hμ) (pair A B) i' ≤
        pair (pair (check (x.Func a)) (check (x.Func b))) i' ∈ᴮ cdot x block μ hμ :=
      bv_rw' (bv_symm (hpairAB i' inf_le_left)) (ϕ := fun w => w ∈ᴮ cdot x block μ hμ)
        (h_congr := B_ext_mem_left) (H_new := inf_le_right)
    have hE' : emb q ⊓ Flypitch.Erdos501.Sem.app (cdot x block μ hμ) (pair A B) i' ≤
        emb q ⊓ pair (pair (check (x.Func a)) (check (x.Func b))) i' ∈ᴮ cdot x block μ hμ :=
      le_inf inf_le_left hE
    refine hE'.trans (inf_mem_cdot_le ?_)
    intro a' b' c' _
    have hcase := eq_pair_cases hx (a := a) (b := b) (a' := a') (b' := b') (i := i')
      (n := colourName x block μ hμ c')
      (F := emb q ⊓ (colVal x block μ hμ a' b' c' ⊓
        pair (pair (check (x.Func a)) (check (x.Func b))) i' =ᴮ
          pair (pair (check (x.Func a')) (check (x.Func b'))) (colourName x block μ hμ c')))
      (inf_le_right.trans inf_le_right)
    rcases hcase with ⟨rfl, rfl, hi⟩ | hbot
    · by_cases hcc : c = c'
      · subst hcc; exact hi
      · exact ((inf_le_inf_left _ inf_le_left).trans
          (le_of_eq (emb_inf_colVal_eq_bot hqc hcc))).trans bot_le
    · exact hbot.trans bot_le

/-! ## Decision lemmas -/

theorem exists_decides_of_app (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    {Γ : CAlg x.Type I block μ hμ} {a b : x.Type} {i : bSet (CAlg x.Type I block μ hμ)}
    {c : Bool}
    (h : Γ ≤ Flypitch.Erdos501.Sem.app (cdot x block μ hμ)
      (pair (check (x.Func a)) (check (x.Func b))) i)
    (hother : ∀ c', c' ≠ c → Γ ⊓ i =ᴮ colourName x block μ hμ c' ≤ ⊥)
    {Γ' : CAlg x.Type I block μ hμ} (hΓ' : ⊥ < Γ') (hle : Γ' ≤ Γ) :
    ∃ q, emb q ≤ Γ' ∧ Decides x block μ hμ q a b c := by
  have hmem : Γ' ≤ pair (pair (check (x.Func a)) (check (x.Func b))) i ∈ᴮ
      cdot x block μ hμ := hle.trans h
  rw [mem_unfold] at hmem
  obtain ⟨⟨⟨a', b', c'⟩, hab'⟩, ht⟩ := nonzero_inf_of_nonzero_le_supr hΓ' hmem
  change ⊥ < Γ' ⊓ (colVal x block μ hμ a' b' c' ⊓
    pair (pair (check (x.Func a)) (check (x.Func b))) i =ᴮ
      pair (pair (check (x.Func a')) (check (x.Func b'))) (colourName x block μ hμ c')) at ht
  set F := Γ' ⊓ (colVal x block μ hμ a' b' c' ⊓
    pair (pair (check (x.Func a)) (check (x.Func b))) i =ᴮ
      pair (pair (check (x.Func a')) (check (x.Func b'))) (colourName x block μ hμ c')) with hFdef
  rcases eq_pair_cases hx (F := F) (inf_le_right.trans inf_le_right) with ⟨rfl, rfl, hi⟩ | hbot
  · by_cases hcc : c' = c
    · subst hcc
      have hFv : F ≤ colVal x block μ hμ a b c' := inf_le_right.trans inf_le_left
      rw [colVal] at hFv
      obtain ⟨⟨q, hq⟩, hFq⟩ := nonzero_inf_of_nonzero_le_supr ht hFv
      obtain ⟨r, hr⟩ := exists_emb_le hFq
      obtain ⟨s, hsr, hsq⟩ := compatible_of_emb_le (hr.trans inf_le_right)
      exact ⟨s, (emb_mono hsr).trans (hr.trans (inf_le_left.trans inf_le_left)), hq.mono hsq⟩
    · exact absurd ((le_inf (inf_le_left.trans hle) hi).trans (hother c' hcc)) (not_le_of_gt ht)
  · exact absurd hbot (not_le_of_gt ht)

/-- If the colour of `(a, b)` is forced to be `1`, conditions deciding blue are
dense below. -/
theorem exists_blue_of_app_one (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    {Γ : CAlg x.Type I block μ hμ} {a b : x.Type} {i : bSet (CAlg x.Type I block μ hμ)}
    (h : Γ ≤ Flypitch.Erdos501.Sem.app (cdot x block μ hμ)
      (pair (check (x.Func a)) (check (x.Func b))) i)
    (hone : Γ ≤ Sem.one i)
    {Γ' : CAlg x.Type I block μ hμ} (hΓ' : ⊥ < Γ') (hle : Γ' ≤ Γ) :
    ∃ q, emb q ≤ Γ' ∧ a ∈ q.last.support ∧ b ∈ q.last.support ∧ q.last.blue a b := by
  obtain ⟨q, hq, ha, hb, hc⟩ := exists_decides_of_app hx (c := true) h (fun c' hc' => by
    have hc'f : c' = false := by cases c' <;> simp_all
    subst hc'f
    have h₁ : Γ ⊓ i =ᴮ colourName x block μ hμ false ≤
        (bSet.empty : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ i := inf_le_left.trans (mem_of_one hone)
    have h₂ : Γ ⊓ i =ᴮ colourName x block μ hμ false ≤
        (bSet.empty : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ bSet.empty :=
      bv_rw' (bv_symm inf_le_right) (ϕ := fun w => (bSet.empty : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ w)
        (h_congr := B_ext_mem_right) (H_new := h₁)
    exact bot_of_mem_empty h₂) hΓ' hle
  exact ⟨q, hq, ha, hb, hc.mpr rfl⟩

/-- If the colour of `(a, b)` is forced to be `0`, conditions deciding red are
dense below. -/
theorem exists_red_of_app_zero (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    {Γ : CAlg x.Type I block μ hμ} {a b : x.Type} {i : bSet (CAlg x.Type I block μ hμ)}
    (h : Γ ≤ Flypitch.Erdos501.Sem.app (cdot x block μ hμ)
      (pair (check (x.Func a)) (check (x.Func b))) i)
    (hzero : Γ ≤ Sem.zero i)
    {Γ' : CAlg x.Type I block μ hμ} (hΓ' : ⊥ < Γ') (hle : Γ' ≤ Γ) :
    ∃ q, emb q ≤ Γ' ∧ a ∈ q.last.support ∧ b ∈ q.last.support ∧ ¬ q.last.blue a b := by
  obtain ⟨q, hq, ha, hb, hc⟩ := exists_decides_of_app hx (c := false) h (fun c' hc' => by
    have hc't : c' = true := by cases c' <;> simp_all
    subst hc't
    apply blueName_eq_empty_le_bot
    exact bv_trans (bv_symm inf_le_right) (inf_le_left.trans hzero)) hΓ' hle
  exact ⟨q, hq, ha, hb, fun hblue => by simpa using hc.mp hblue⟩

end GenericColouring

end Erdos1220Full

#print axioms Erdos1220Full.GenericColouring.Decides.mono
#print axioms Erdos1220Full.GenericColouring.exists_le_decides
#print axioms Erdos1220Full.GenericColouring.decides_unique
#print axioms Erdos1220Full.GenericColouring.emb_inf_colVal_eq_bot
#print axioms Erdos1220Full.GenericColouring.one_blueName
#print axioms Erdos1220Full.GenericColouring.colouring_cdot
#print axioms Erdos1220Full.GenericColouring.exists_decides_of_app
#print axioms Erdos1220Full.GenericColouring.exists_blue_of_app_one
#print axioms Erdos1220Full.GenericColouring.exists_red_of_app_zero
