import Erdos1220Full.ChainPreservation

/-!
# Generic cardinal preservation in `V 𝔹`

Boolean-valued predicates mirroring the formulas of `Statement1220.lean`
(`leqF`, `ordF`, `cardinalF`, `cofinalF`) are defined on names, and the
following preservation results are proved from *abstract* hypotheses on the
complete Boolean algebra `𝔹`:

* `ChainCondition θ 𝔹` with `θ` regular: no ground cardinal `lam ≥ θ` is
  collapsed, i.e. `⊤ ≤ cardinalB (check (card_ex lam))`.
* `DistribHyp ν 𝔹` (`ν`-many choices can be made simultaneously below any
  nonzero element): no ground cardinal `lam` all of whose smaller ordinals have
  cardinality `≤ ν` is collapsed, and no small ground ordinal maps cofinally
  into a ground ordinal of larger cofinality.
* Absoluteness of ground cofinal subsets and ground injections.
-/

open Cardinal Set Flypitch bSet Lattice

universe u

namespace Erdos1220Full.CardB

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-! ### Predicates mirroring `Statement1220.lean` -/

/-- `f(x) = y` (`appF`). -/
abbrev appB (f x y : bSet 𝔹) : 𝔹 := pair x y ∈ᴮ f

/-- `f` is a function from `dom` to `cod` (`isFunF`). -/
def isFunB (dom cod f : bSet 𝔹) : 𝔹 :=
  ⨅ x, (x ∈ᴮ dom) ⟹ (⨆ y, y ∈ᴮ cod ⊓ (appB f x y ⊓ ⨅ y', (appB f x y') ⟹ (y' =ᴮ y)))

/-- Injectivity on `A` (the second conjunct of `leqF`). -/
def injOnB (A f : bSet 𝔹) : 𝔹 :=
  ⨅ x, (x ∈ᴮ A) ⟹ (⨅ x', (x' ∈ᴮ A) ⟹ (⨅ y, (appB f x y) ⟹ ((appB f x' y) ⟹ (x =ᴮ x'))))

/-- `|A| ≤ |B|` (`leqF`). -/
def leqB (A B : bSet 𝔹) : 𝔹 := ⨆ f, isFunB A B f ⊓ injOnB A f

/-- `a` is an ordinal (`ordF`): trichotomy, well-foundedness, transitivity. -/
def ordB (a : bSet 𝔹) : 𝔹 :=
  ((⨅ y, (y ∈ᴮ a) ⟹ (⨅ z, (z ∈ᴮ a) ⟹ ((y =ᴮ z ⊔ y ∈ᴮ z) ⊔ z ∈ᴮ y))) ⊓
    (⨅ y, (⨅ z, (z ∈ᴮ y) ⟹ (z ∈ᴮ a)) ⟹
      ((y =ᴮ (∅ : bSet 𝔹))ᶜ ⟹ (⨆ z, z ∈ᴮ y ⊓ ⨅ w, (w ∈ᴮ y) ⟹ (w ∈ᴮ z)ᶜ)))) ⊓
  (⨅ y, (y ∈ᴮ a) ⟹ (⨅ z, (z ∈ᴮ y) ⟹ (z ∈ᴮ a)))

/-- `k` is a cardinal (`cardinalF`). -/
def cardinalB (k : bSet 𝔹) : 𝔹 := ordB k ⊓ ⨅ a, (a ∈ᴮ k) ⟹ (leqB k a)ᶜ

/-- `S` is cofinal in `l` (`cofinalF`). -/
def cofinalB (S l : bSet 𝔹) : 𝔹 :=
  ⨅ b, (b ∈ᴮ l) ⟹ (⨆ g, g ∈ᴮ S ⊓ (b ∈ᴮ g ⊔ b =ᴮ g))

/-- `S ⊆ l` (`subsetF`). -/
def subsetB (S l : bSet 𝔹) : 𝔹 := ⨅ z, (z ∈ᴮ S) ⟹ (z ∈ᴮ l)

/-- `g` is a function from `D` to `l` with cofinal range. -/
def cofMapB (D l g : bSet 𝔹) : 𝔹 :=
  isFunB D l g ⊓ ⨅ b, (b ∈ᴮ l) ⟹ (⨆ c, c ∈ᴮ D ⊓ ⨆ d, appB g c d ⊓ (b ∈ᴮ d ⊔ b =ᴮ d))

theorem ordB_eq_Ord (a : bSet 𝔹) : ordB a = Ord a := by
  simp only [ordB, bSet.Ord, epsilon_well_orders, epsilon_trichotomy, epsilon_well_founded,
    is_transitive, subset_unfold']

theorem subsetB_eq (S l : bSet 𝔹) : subsetB S l = S ⊆ᴮ l := by
  rw [subset_unfold']; rfl

/-! ### Extensionality -/

theorem B_ext_leqB_right (A : bSet 𝔹) : B_ext (fun B => leqB A B) := by
  unfold leqB isFunB
  exact B_ext_iSup (h := fun f => B_ext_inf
    (B_ext_iInf (h := fun x => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun y => B_ext_inf B_ext_mem_right B_ext_const))))
    B_ext_const)

theorem leqB_congr_right (A : bSet 𝔹) {B B' : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ B =ᴮ B')
    (h' : Γ ≤ leqB A B) : Γ ≤ leqB A B' :=
  le_trans (le_inf h h') (B_ext_leqB_right A B B')

theorem leqB_check_congr (A : bSet 𝔹) {a b : PSet.{u}} (h : PSet.Equiv a b) :
    leqB A (check a : bSet 𝔹) = leqB A (check b) := by
  apply le_antisymm
  · exact leqB_congr_right A (check_bv_eq h) le_rfl
  · exact leqB_congr_right A (check_bv_eq (PSet.Equiv.symm h)) le_rfl

/-! ### Using the predicates at check names -/

theorem isFunB_total_check {x y : PSet.{u}} {f : bSet 𝔹} {Γ : 𝔹}
    (hF : Γ ≤ isFunB (check y) (check x) f) (j : y.Type) :
    Γ ≤ ⨆ i : (check x : bSet 𝔹).type,
      appB f (check (y.Func j)) (check (x.Func (check_cast i))) := by
  have h1 : Γ ≤ ⨆ z, z ∈ᴮ (check x : bSet 𝔹) ⊓ (appB f (check (y.Func j)) z ⊓
      ⨅ y', (appB f (check (y.Func j)) y') ⟹ (y' =ᴮ z)) :=
    le_trans (le_inf (hF.trans (iInf_le _ (check (y.Func j)))) mem_check_of_mem) bv_imp_elim
  have h2 : Γ ≤ ⨆ z, z ∈ᴮ (check x : bSet 𝔹) ⊓ appB f (check (y.Func j)) z :=
    h1.trans (iSup_mono fun z => inf_le_inf_left _ inf_le_left)
  rw [← @bounded_exists 𝔹 _ (check x) (fun z => appB f (check (y.Func j)) z)
    (h_congr := B_ext_pair_mem_right)] at h2
  simpa only [check_bval_top, top_inf_eq, check_func] using h2

theorem injOnB_check {y : PSet.{u}} {f z : bSet 𝔹} {Γ : 𝔹}
    (hI : Γ ≤ injOnB (check y) f) (j j' : y.Type)
    (h1 : Γ ≤ appB f (check (y.Func j)) z) (h2 : Γ ≤ appB f (check (y.Func j')) z) :
    Γ ≤ (check (y.Func j) : bSet 𝔹) =ᴮ check (y.Func j') := by
  have a1 := le_trans (le_inf (hI.trans (iInf_le _ (check (y.Func j)))) mem_check_of_mem)
    bv_imp_elim
  have a2 := le_trans (le_inf (a1.trans (iInf_le _ (check (y.Func j')))) mem_check_of_mem)
    bv_imp_elim
  have a3 := le_trans (le_inf (a2.trans (iInf_le _ z)) h1) bv_imp_elim
  exact le_trans (le_inf a3 h2) bv_imp_elim

/-! ### Chain condition -/

/-- If every map from `y` to `x` has a fiber of size `≥ θ`, then under the
`θ`-chain condition `check y` does not inject into `check x`. -/
theorem leqB_check_eq_bot_of_chainCondition {θ : Cardinal.{u}} (hcc : ChainCondition θ 𝔹)
    (x y : PSet.{u}) (hy : ∀ i j, i ≠ j → ¬ PSet.Equiv (y.Func i) (y.Func j))
    (hfib : ∀ g : y.Type → x.Type, ∃ ξ, θ ≤ #(g ⁻¹' {ξ})) :
    leqB (check y : bSet 𝔹) (check x) = ⊥ := by
  classical
  apply le_bot_iff.mp
  apply poset_yoneda
  intro Γ hΓ
  by_cases h0 : Γ = ⊥
  · exact h0.le
  have hpos : ⊥ < Γ := bot_lt_iff_ne_bot.mpr h0
  obtain ⟨f, hf⟩ := nonzero_wit' hpos
    (show Γ ≤ ⨆ f, isFunB (check y) (check x) f ⊓ injOnB (check y) f from hΓ)
  set Γ₀ := isFunB (check y : bSet 𝔹) (check x) f ⊓ injOnB (check y) f with hΓ₀
  have hpos0 : ⊥ < Γ₀ := lt_of_lt_of_le hf inf_le_left
  have htot := fun j => isFunB_total_check (x := x) (y := y) (Γ := Γ₀) inf_le_left j
  choose g hg using fun j => nonzero_inf_of_nonzero_le_supr hpos0 (htot j)
  obtain ⟨ξ, hξ⟩ := hfib (fun j => check_cast (g j))
  let a : ((fun j => check_cast (g j)) ⁻¹' {ξ}) → 𝔹 := fun j =>
    Γ₀ ⊓ appB f (check (y.Func j.1)) (check (x.Func ξ))
  have hsmall := hcc _ a
    (fun j => by
      have h := hg j.1
      have hj : check_cast (g j.1) = ξ := j.2
      simp only [a]
      rwa [hj] at h)
    (fun j j' hjj => by
      apply le_trans _ (le_of_eq (check_bv_eq_bot_of_not_equiv
        (hy j.1 j'.1 (fun h => hjj (Subtype.ext h)))))
      exact injOnB_check (inf_le_left.trans (inf_le_left.trans inf_le_right)) j.1 j'.1
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  exact absurd (hξ.trans_lt hsmall) (lt_irrefl _)

/-- Fibers of maps from a cardinal `lam ≥ θ` onto a smaller ordinal. -/
theorem exists_large_fiber {θ lam : Cardinal.{u}} (hθ : θ.IsRegular) (hθlam : θ ≤ lam)
    {o : Ordinal.{u}} (ho : o < lam.ord)
    (g : (PSet.card_ex lam).Type → (PSet.ordinalMk o).Type) :
    ∃ ξ, θ ≤ #(g ⁻¹' {ξ}) := by
  have hdom : #(PSet.card_ex lam).Type = lam := by
    rw [PSet.card_ex, PSet.ordinalMk_card, Cardinal.card_ord]
  have hcod : #(PSet.ordinalMk o).Type = o.card := PSet.ordinalMk_card
  have hlt : o.card < lam := Cardinal.lt_ord.mp ho
  rcases lt_or_ge o.card θ with hsm | hbig
  · apply Cardinal.infinite_pigeonhole_card g θ (hθlam.trans_eq hdom.symm) hθ.aleph0_le
    rw [hcod, hθ.cof_ord]
    exact hsm
  · obtain ⟨ξ, hξ⟩ := Cardinal.infinite_pigeonhole_card_lt g (by rw [hdom, hcod]; exact hlt)
      (by rw [hdom]; exact hθ.aleph0_le.trans hθlam)
    exact ⟨ξ, (hbig.trans_eq hcod.symm).trans hξ.le⟩

theorem card_ex_inj (lam : Cardinal.{u}) :
    ∀ i j, i ≠ j → ¬ PSet.Equiv ((PSet.card_ex lam).Func i) ((PSet.card_ex lam).Func j) :=
  PSet.ordinalMk_inj _

/-- Members of `card_ex lam` are equivalent to smaller von Neumann ordinals. -/
theorem card_ex_func_equiv (lam : Cardinal.{u}) (i : (PSet.card_ex lam).Type) :
    ∃ o < lam.ord, PSet.Equiv ((PSet.card_ex lam).Func i) (PSet.ordinalMk o) :=
  PSet.mem_ordinalMk_iff.mp (PSet.func_mem _ i)

/-- The non-collapse half of `cardinalB`, from its value on check members. -/
theorem noncollapse_of_members (k : PSet.{u})
    (hk : ∀ i : k.Type, leqB (check k : bSet 𝔹) (check (k.Func i)) = ⊥) :
    (⊤ : 𝔹) ≤ ⨅ a, (a ∈ᴮ (check k : bSet 𝔹)) ⟹ (leqB (check k) a)ᶜ := by
  rw [← @bounded_forall 𝔹 _ (check k) (fun a => (leqB (check k : bSet 𝔹) a)ᶜ)
    (h_congr := B_ext_neg (h := B_ext_leqB_right _))]
  apply le_iInf
  intro i
  rw [check_bval_top, check_func, hk]
  simp [imp]

theorem cardinalB_of_members (k : PSet.{u}) (hk : PSet.Ord k)
    (hmem : ∀ i : k.Type, leqB (check k : bSet 𝔹) (check (k.Func i)) = ⊥) :
    (⊤ : 𝔹) ≤ cardinalB (check k) :=
  le_inf (by rw [ordB_eq_Ord]; exact check_Ord hk) (noncollapse_of_members k hmem)

/-- **(1) Chain condition.** Every ground cardinal `lam ≥ θ` remains a cardinal. -/
theorem cardinalB_card_ex_of_chainCondition {θ : Cardinal.{u}} (hcc : ChainCondition θ 𝔹)
    (hθ : θ.IsRegular) {lam : Cardinal.{u}} (hθlam : θ ≤ lam) :
    (⊤ : 𝔹) ≤ cardinalB (check (PSet.card_ex lam)) := by
  apply cardinalB_of_members _ (PSet.Ord_mk _)
  intro i
  obtain ⟨o, ho, hequiv⟩ := card_ex_func_equiv lam i
  refine (leqB_check_congr (check (PSet.card_ex lam)) hequiv).trans ?_
  exact leqB_check_eq_bot_of_chainCondition hcc _ _ (card_ex_inj lam)
    (exists_large_fiber hθ hθlam ho)

/-! ### Distributivity -/

/-- `ν` many choices can be made simultaneously below any nonzero element. -/
def DistribHyp (ν : Cardinal.{u}) (𝔹 : Type u) [NontrivialCompleteBooleanAlgebra 𝔹] : Prop :=
  ∀ (J : Type u), #J ≤ ν → ∀ (ι : J → Type u) (φ : ∀ j, ι j → 𝔹) (Γ : 𝔹), ⊥ < Γ →
    (∀ j, Γ ≤ ⨆ i, φ j i) → ∃ Δ : 𝔹, ⊥ < Δ ∧ Δ ≤ Γ ∧ ∃ c : ∀ j, ι j, ∀ j, Δ ≤ φ j (c j)

/-- Under `ν`-distributivity, a check set does not inject into a smaller
check set of size `≤ ν`. -/
theorem leqB_check_eq_bot_of_distrib {ν : Cardinal.{u}} (hd : DistribHyp ν 𝔹)
    (x y : PSet.{u}) (hy : ∀ i j, i ≠ j → ¬ PSet.Equiv (y.Func i) (y.Func j))
    (hxν : #x.Type ≤ ν) (hxy : #x.Type < #y.Type) :
    leqB (check y : bSet 𝔹) (check x) = ⊥ := by
  classical
  apply le_bot_iff.mp
  apply poset_yoneda
  intro Γ hΓ
  by_cases h0 : Γ = ⊥
  · exact h0.le
  have hpos : ⊥ < Γ := bot_lt_iff_ne_bot.mpr h0
  obtain ⟨f, hf⟩ := nonzero_wit' hpos
    (show Γ ≤ ⨆ f, isFunB (check y) (check x) f ⊓ injOnB (check y) f from hΓ)
  set Γ₀ := isFunB (check y : bSet 𝔹) (check x) f ⊓ injOnB (check y) f with hΓ₀
  have hpos0 : ⊥ < Γ₀ := lt_of_lt_of_le hf inf_le_left
  let S : x.Type → 𝔹 := fun γ => ⨆ β : y.Type, appB f (check (y.Func β)) (check (x.Func γ))
  let φ : ∀ γ : x.Type, Option y.Type → 𝔹 := fun γ o =>
    match o with
    | some β => appB f (check (y.Func β)) (check (x.Func γ))
    | none => (S γ)ᶜ
  obtain ⟨Δ, hΔpos, hΔle, c, hc⟩ := hd x.Type hxν (fun _ => Option y.Type) φ Γ₀ hpos0
    (fun γ => le_trans (bv_em (S γ)) (sup_le
      (iSup_le fun β => le_iSup_of_le (some β) le_rfl) (le_iSup_of_le none le_rfl)))
  have hfree : ∃ β : y.Type, ∀ γ, c γ ≠ some β := by
    by_contra hcon
    push Not at hcon
    choose s hs using hcon
    have hinj : Function.Injective s := by
      intro β β' h
      have := (hs β).symm.trans ((congrArg c h).trans (hs β'))
      exact Option.some_injective _ this
    exact absurd (Cardinal.mk_le_of_injective hinj) (not_le.mpr hxy)
  obtain ⟨β, hβ⟩ := hfree
  obtain ⟨i, hi⟩ := nonzero_inf_of_nonzero_le_supr hΔpos
    (hΔle.trans (isFunB_total_check (x := x) (y := y) inf_le_left β))
  set γ := check_cast i with hγ
  have hbot : Δ ⊓ appB f (check (y.Func β)) (check (x.Func γ)) ≤ ⊥ := by
    have hcγ := hc γ
    cases hco : c γ with
    | none =>
      rw [hco] at hcγ
      have hS : appB f (check (y.Func β)) (check (x.Func γ)) ≤ S γ :=
        le_iSup_of_le β le_rfl
      calc Δ ⊓ appB f (check (y.Func β)) (check (x.Func γ))
          ≤ (S γ)ᶜ ⊓ S γ := inf_le_inf hcγ hS
        _ = ⊥ := compl_inf_self _
    | some β'' =>
      rw [hco] at hcγ
      have hne : β ≠ β'' := fun h => hβ γ (h ▸ hco)
      apply le_trans _ (le_of_eq (check_bv_eq_bot_of_not_equiv (hy β β'' hne)))
      exact injOnB_check ((inf_le_left.trans hΔle).trans inf_le_right) β β''
        inf_le_right (inf_le_left.trans hcγ)
  exact absurd (lt_of_lt_of_le hi hbot) (lt_irrefl _)

/-- **(2a) Distributivity.** A ground cardinal `lam` all of whose smaller
ordinals have size `≤ ν` remains a cardinal (e.g. every `lam ≤ ν⁺`). -/
theorem cardinalB_card_ex_of_distrib {ν : Cardinal.{u}} (hd : DistribHyp ν 𝔹)
    {lam : Cardinal.{u}} (hsmall : ∀ o < lam.ord, o.card ≤ ν) :
    (⊤ : 𝔹) ≤ cardinalB (check (PSet.card_ex lam)) := by
  apply cardinalB_of_members _ (PSet.Ord_mk _)
  intro i
  obtain ⟨o, ho, hequiv⟩ := card_ex_func_equiv lam i
  refine (leqB_check_congr (check (PSet.card_ex lam)) hequiv).trans ?_
  apply leqB_check_eq_bot_of_distrib hd _ _ (card_ex_inj lam)
  · rw [PSet.ordinalMk_card]; exact hsmall o ho
  · rw [PSet.ordinalMk_card, PSet.card_ex, PSet.ordinalMk_card, Cardinal.card_ord]
    exact Cardinal.lt_ord.mp ho

/-- **Combined.** If `θ ≤ ν⁺`, the `θ`-chain condition together with
`ν`-distributivity preserves every ground cardinal. -/
theorem cardinalB_card_ex_all {θ ν : Cardinal.{u}} (hcc : ChainCondition θ 𝔹)
    (hθ : θ.IsRegular) (hd : DistribHyp ν 𝔹) (hθν : θ ≤ Order.succ ν) (lam : Cardinal.{u}) :
    (⊤ : 𝔹) ≤ cardinalB (check (PSet.card_ex lam)) := by
  rcases le_or_gt θ lam with h | h
  · exact cardinalB_card_ex_of_chainCondition hcc hθ h
  · apply cardinalB_card_ex_of_distrib hd
    intro o ho
    exact Order.lt_succ_iff.mp ((Cardinal.lt_ord.mp ho).trans_le (h.le.trans hθν))


/-! ### Regularity: no small cofinal maps -/

theorem isFunB_unique {D l g a d e : bSet 𝔹} {Γ : 𝔹} (hF : Γ ≤ isFunB D l g)
    (ha : Γ ≤ a ∈ᴮ D) (hd : Γ ≤ appB g a d) (he : Γ ≤ appB g a e) : Γ ≤ d =ᴮ e := by
  have h1 : Γ ≤ ⨆ y, y ∈ᴮ l ⊓ (appB g a y ⊓ ⨅ y', (appB g a y') ⟹ (y' =ᴮ y)) :=
    le_trans (le_inf (hF.trans (iInf_le _ a)) ha) bv_imp_elim
  refine le_trans (le_inf le_rfl h1) (le_trans (le_of_eq (inf_iSup_eq _ _)) (iSup_le fun y => ?_))
  have hu : Γ ⊓ (y ∈ᴮ l ⊓ (appB g a y ⊓ ⨅ y', (appB g a y') ⟹ (y' =ᴮ y))) ≤
      ⨅ y', (appB g a y') ⟹ (y' =ᴮ y) :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  have hdy := le_trans (le_inf (hu.trans (iInf_le _ d)) (inf_le_left.trans hd)) bv_imp_elim
  have hey := le_trans (le_inf (hu.trans (iInf_le _ e)) (inf_le_left.trans he)) bv_imp_elim
  exact bv_trans hdy (bv_symm hey)

/-- A bound above a small family of ordinals inside an ordinal of larger cofinality. -/
theorem exists_strict_bound {J : Type u} {κo : Ordinal.{u}} (hJ : #J < κo.cof)
    (ordOf : J → Ordinal.{u}) (hlt : ∀ γ, ordOf γ < κo) :
    ∃ σ, σ < κo ∧ ∀ γ, ordOf γ < σ := by
  by_cases hne : Nonempty J
  · have hsucc : ∀ γ, Order.succ (ordOf γ) < κo := by
      intro γ
      by_contra hle
      push Not at hle
      have heq : κo = Order.succ (ordOf γ) := le_antisymm hle (Order.succ_le_of_lt (hlt γ))
      have h1 : κo.cof = 1 := by rw [heq, Ordinal.cof_succ]
      have hpos : (1 : Cardinal) ≤ #J :=
        Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero_iff.mpr hne)
      rw [h1] at hJ
      exact absurd (hpos.trans_lt hJ) (lt_irrefl _)
    refine ⟨⨆ γ, Order.succ (ordOf γ), Ordinal.iSup_lt_of_lt_cof hJ hsucc, fun γ => ?_⟩
    exact (Order.lt_succ _).trans_le (Ordinal.le_iSup (fun γ => Order.succ (ordOf γ)) γ)
  · have hκ : κo ≠ 0 := by
      rintro rfl
      rw [Ordinal.cof_zero] at hJ
      exact absurd hJ (by simp)
    exact ⟨0, pos_iff_ne_zero.mpr hκ, fun γ => absurd ⟨γ⟩ hne⟩

/-- **(2b) Distributivity.** No function from a ground ordinal of size `≤ ν`
into a ground ordinal of larger cofinality has cofinal range in `V 𝔹`. -/
theorem cofMapB_check_eq_bot {ν : Cardinal.{u}} (hd : DistribHyp ν 𝔹) {o κo : Ordinal.{u}}
    (hoν : o.card ≤ ν) (hcof : o.card < κo.cof) (g : bSet 𝔹) :
    cofMapB (check (PSet.ordinalMk o)) (check (PSet.ordinalMk κo)) g = (⊥ : 𝔹) := by
  classical
  set x := PSet.ordinalMk o with hx
  set y := PSet.ordinalMk κo with hy
  apply le_bot_iff.mp
  apply poset_yoneda
  intro Γ hΓ
  by_cases h0 : Γ = ⊥
  · exact h0.le
  have hpos : ⊥ < Γ := bot_lt_iff_ne_bot.mpr h0
  have hF : Γ ≤ isFunB (check x) (check y) g := hΓ.trans inf_le_left
  have hC : Γ ≤ ⨅ b, (b ∈ᴮ (check y : bSet 𝔹)) ⟹
      (⨆ c, c ∈ᴮ (check x : bSet 𝔹) ⊓ ⨆ d, appB g c d ⊓ (b ∈ᴮ d ⊔ b =ᴮ d)) :=
    hΓ.trans inf_le_right
  have hxcard : #x.Type = o.card := PSet.ordinalMk_card
  obtain ⟨Δ, hΔpos, hΔle, c, hc⟩ := hd x.Type (hxcard ▸ hoν)
    (fun _ => (check y : bSet 𝔹).type)
    (fun γ i => appB g (check (x.Func γ)) (check (y.Func (check_cast i)))) Γ hpos
    (fun γ => isFunB_total_check (x := y) (y := x) hF γ)
  choose ordOf hordlt hordeq using fun β : y.Type => PSet.mem_ordinalMk_iff.mp (PSet.func_mem y β)
  obtain ⟨σ, hσ, hσbound⟩ := exists_strict_bound (J := x.Type) (κo := κo)
    (hxcard ▸ hcof) (fun γ => ordOf (check_cast (c γ))) (fun γ => hordlt _)
  obtain ⟨β₀, hβ₀⟩ := PSet.mem_unfold.mp (PSet.mk_mem_mk_of_lt hσ)
  have hordβ₀ : σ = ordOf β₀ := PSet.eq_of_mk_equiv (hβ₀.trans (hordeq β₀))
  set b : bSet 𝔹 := check (y.Func β₀) with hbdef
  have hb : Δ ≤ ⨆ c', c' ∈ᴮ (check x : bSet 𝔹) ⊓ ⨆ d, appB g c' d ⊓ (b ∈ᴮ d ⊔ b =ᴮ d) :=
    le_trans (le_inf ((hΔle.trans hC).trans (iInf_le _ b)) mem_check_of_mem) bv_imp_elim
  rw [← @bounded_exists 𝔹 _ (check x) (fun c' => ⨆ d, appB g c' d ⊓ (b ∈ᴮ d ⊔ b =ᴮ d))
    (h_congr := B_ext_iSup (h := fun d => B_ext_inf B_ext_pair_mem_left B_ext_const))] at hb
  simp only [check_bval_top, top_inf_eq, check_func] at hb
  have hbot : Δ ≤ ⊥ := by
    refine le_trans (le_inf le_rfl hb) ?_
    rw [inf_iSup_eq]
    refine iSup_le fun i => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun d => ?_
    set γ := check_cast i with hγ
    set e : bSet 𝔹 := check (y.Func (check_cast (c γ))) with he
    have hde : Δ ⊓ (appB g (check (x.Func γ)) d ⊓ (b ∈ᴮ d ⊔ b =ᴮ d)) ≤ d =ᴮ e :=
      isFunB_unique ((inf_le_left.trans hΔle).trans hF) mem_check_of_mem
        (inf_le_right.trans inf_le_left) (inf_le_left.trans (hc γ))
    have hbe : Δ ⊓ (appB g (check (x.Func γ)) d ⊓ (b ∈ᴮ d ⊔ b =ᴮ d)) ≤ b ∈ᴮ e ⊔ b =ᴮ e :=
      bv_rw' (bv_symm hde) (ϕ := fun z => b ∈ᴮ z ⊔ b =ᴮ z)
        (h_congr := B_ext_sup (h₁ := B_ext_mem_right) (h₂ := B_ext_bv_eq_right))
        (H_new := inf_le_right.trans inf_le_right)
    have hlt := hσbound γ
    rw [hordβ₀] at hlt
    have hnm : ¬ (y.Func β₀ ∈ y.Func (check_cast (c γ))) := by
      intro hmem
      have h1 := (PSet.Mem.congr_left (hordeq β₀)).mp hmem
      have h2 := (PSet.Mem.congr_right (hordeq _)).mp h1
      exact absurd (PSet.ordinalMk_lt_of_mem h2) (not_lt.mpr hlt.le)
    have hne : ¬ PSet.Equiv (y.Func β₀) (y.Func (check_cast (c γ))) := by
      intro heqv
      have := PSet.eq_of_mk_equiv ((hordeq β₀).symm.trans (heqv.trans (hordeq _)))
      exact absurd this (ne_of_gt hlt)
    refine hbe.trans (sup_le ?_ ?_)
    · exact check_not_mem hnm le_rfl
    · exact le_of_eq (check_bv_eq_bot_of_not_equiv hne)
  exact absurd (lt_of_lt_of_le hΔpos hbot) (lt_irrefl _)

/-- Regular-cardinal form of (2b). -/
theorem cofMapB_card_ex_eq_bot {ν : Cardinal.{u}} (hd : DistribHyp ν 𝔹) {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {o : Ordinal.{u}} (hoν : o.card ≤ ν) (hoκ : o.card < κ) (g : bSet 𝔹) :
    cofMapB (check (PSet.ordinalMk o)) (check (PSet.card_ex κ)) g = (⊥ : 𝔹) :=
  cofMapB_check_eq_bot hd hoν (by rw [hκ.cof_ord]; exact hoκ) g

/-! ### Absoluteness of ground injections and cofinal subsets (for (3)) -/

theorem is_func'_inj_le_leqB_body (A B f : bSet 𝔹) :
    is_func' A B f ⊓ is_inj f ≤ isFunB A B f ⊓ injOnB A f := by
  set Γ := is_func' A B f ⊓ is_inj f
  refine le_inf ?_ ?_
  · refine le_iInf fun a => ?_
    rw [← deduction]
    have htot : Γ ⊓ a ∈ᴮ A ≤ ⨆ w, w ∈ᴮ B ⊓ pair a w ∈ᴮ f :=
      le_trans (le_inf ((inf_le_left.trans (inf_le_left.trans inf_le_right)).trans
        (iInf_le _ a)) inf_le_right) bv_imp_elim
    refine le_trans (le_inf le_rfl htot) (le_trans (le_of_eq (inf_iSup_eq _ _))
      (iSup_mono fun w => ?_))
    refine le_inf (inf_le_right.trans inf_le_left) (le_inf (inf_le_right.trans inf_le_right) ?_)
    refine le_iInf fun y' => ?_
    rw [← deduction]
    have hfun : (Γ ⊓ a ∈ᴮ A ⊓ (w ∈ᴮ B ⊓ pair a w ∈ᴮ f)) ⊓ appB f a y' ≤ is_func f :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    have h1 := hfun.trans ((iInf_le _ a).trans ((iInf_le _ a).trans ((iInf_le _ y').trans
      (iInf_le _ w))))
    have h2 := le_trans (le_inf h1 (le_inf inf_le_right
      (inf_le_left.trans (inf_le_right.trans inf_le_right)))) bv_imp_elim
    exact le_trans (le_inf h2 bv_refl) bv_imp_elim
  · refine le_iInf fun a => ?_
    rw [← deduction]
    refine le_iInf fun a' => ?_
    rw [← deduction]
    refine le_iInf fun z => ?_
    rw [← deduction]
    rw [← deduction]
    have hinj : Γ ⊓ a ∈ᴮ A ⊓ a' ∈ᴮ A ⊓ appB f a z ⊓ appB f a' z ≤ is_inj f :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
    have h1 := hinj.trans ((iInf_le _ a).trans ((iInf_le _ a').trans ((iInf_le _ z).trans
      (iInf_le _ z))))
    exact le_trans (le_inf h1 (le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      bv_refl)) bv_imp_elim

theorem injects_into_le_leqB (A B : bSet 𝔹) : injects_into A B ≤ leqB A B :=
  iSup_le fun f => le_iSup_of_le f (is_func'_inj_le_leqB_body A B f)

/-- A ground injection gives `|x̌| ≤ |y̌|` in `V 𝔹`. -/
theorem leqB_check_of_injects {x y : PSet.{u}} (h : PSet.injects_into x y) :
    (⊤ : 𝔹) ≤ leqB (check x) (check y) :=
  (check_injects_into h).trans (injects_into_le_leqB _ _)

/-- A ground subset stays a subset. -/
theorem subsetB_check {S l : PSet.{u}} (h : S ⊆ l) :
    (⊤ : 𝔹) ≤ subsetB (check S) (check l) := by
  rw [subsetB_eq]; exact check_subset h

/-- **(3) A ground cofinal subset stays cofinal.** -/
theorem cofinalB_check {S l : PSet.{u}}
    (h : ∀ i : l.Type, ∃ j : S.Type, l.Func i ∈ S.Func j ∨ PSet.Equiv (l.Func i) (S.Func j)) :
    (⊤ : 𝔹) ≤ cofinalB (check S) (check l) := by
  unfold cofinalB
  rw [← @bounded_forall 𝔹 _ (check l)
    (fun b => ⨆ g, g ∈ᴮ (check S : bSet 𝔹) ⊓ (b ∈ᴮ g ⊔ b =ᴮ g))
    (h_congr := B_ext_iSup (h := fun g => B_ext_inf B_ext_const
      (B_ext_sup (h₁ := B_ext_mem_left) (h₂ := B_ext_bv_eq_left))))]
  refine le_iInf fun i => ?_
  rw [check_bval_top, check_func]
  obtain ⟨j, hj⟩ := h (check_cast i)
  have hbody : (⊤ : 𝔹) ≤ ⨆ g, g ∈ᴮ (check S : bSet 𝔹) ⊓
      ((check (l.Func (check_cast i)) : bSet 𝔹) ∈ᴮ g ⊔ check (l.Func (check_cast i)) =ᴮ g) := by
    refine le_iSup_of_le (check (S.Func j)) (le_inf mem_check_of_mem ?_)
    rcases hj with hm | he
    · exact le_sup_of_le_left (check_mem hm)
    · exact le_sup_of_le_right (check_bv_eq he)
  simpa [imp] using hbody


/-! ### ω-sequences: `μ ^ ℵ₀ < κ` transfers from a check function set (for (4)) -/

/-- `f` is a function from `D` to `C` as a set of pairs (`fnF`). -/
def fnB (D C f : bSet 𝔹) : 𝔹 :=
  (⨅ z : bSet 𝔹, z ∈ᴮ f ⟹ ⨆ x : bSet 𝔹, x ∈ᴮ D ⊓ ⨆ y : bSet 𝔹, y ∈ᴮ C ⊓ z =ᴮ pair x y) ⊓
    ⨅ x : bSet 𝔹, x ∈ᴮ D ⟹ ⨆ y : bSet 𝔹, appB f x y ⊓ ⨅ y' : bSet 𝔹, appB f x y' ⟹ y' =ᴮ y

/-- `|μ| ^ ℵ₀ < |k|` (`powLtF`). -/
def powLtB (μ k : bSet 𝔹) : 𝔹 :=
  ⨆ α : bSet 𝔹, α ∈ᴮ k ⊓ ⨆ h : bSet 𝔹,
    (⨅ f : bSet 𝔹, fnB bSet.omega μ f ⟹ ⨆ b : bSet 𝔹, b ∈ᴮ α ⊓ appB h f b) ⊓
    ⨅ f : bSet 𝔹, ⨅ f' : bSet 𝔹, ⨅ b : bSet 𝔹,
      fnB bSet.omega μ f ⟹ (fnB bSet.omega μ f' ⟹ (appB h f b ⟹ (appB h f' b ⟹ f =ᴮ f')))

theorem fnB_mem {D C f a b : bSet 𝔹} {Γ : 𝔹} (hf : Γ ≤ fnB D C f) (hab : Γ ≤ pair a b ∈ᴮ f) :
    Γ ≤ a ∈ᴮ D ⊓ b ∈ᴮ C := by
  have h := le_trans (le_inf ((hf.trans inf_le_left).trans (iInf_le _ (pair a b))) hab)
    bv_imp_elim
  refine h.trans (iSup_le fun x => ?_)
  rw [inf_iSup_eq]
  refine iSup_le fun y => ?_
  have heq : x ∈ᴮ D ⊓ (y ∈ᴮ C ⊓ pair a b =ᴮ pair x y) ≤ pair a b =ᴮ pair x y :=
    inf_le_right.trans inf_le_right
  obtain ⟨hax, hby⟩ := eq_of_eq_pair heq
  refine le_inf ?_ ?_
  · exact bv_rw' hax (ϕ := fun w => w ∈ᴮ D) (h_congr := B_ext_mem_left) (H_new := inf_le_left)
  · exact bv_rw' hby (ϕ := fun w => w ∈ᴮ C) (h_congr := B_ext_mem_left)
      (H_new := inf_le_right.trans inf_le_left)

theorem uniq_of {f a d e : bSet 𝔹} {Γ : 𝔹}
    (hu : Γ ≤ ⨆ y : bSet 𝔹, appB f a y ⊓ ⨅ y' : bSet 𝔹, appB f a y' ⟹ y' =ᴮ y)
    (hd : Γ ≤ appB f a d) (he : Γ ≤ appB f a e) : Γ ≤ d =ᴮ e := by
  refine le_trans (le_inf le_rfl hu) (le_trans (le_of_eq (inf_iSup_eq _ _)) (iSup_le fun y => ?_))
  have hU : Γ ⊓ (appB f a y ⊓ ⨅ y' : bSet 𝔹, appB f a y' ⟹ y' =ᴮ y) ≤
      ⨅ y' : bSet 𝔹, appB f a y' ⟹ y' =ᴮ y := inf_le_right.trans inf_le_right
  have hdy := le_trans (le_inf (hU.trans (iInf_le _ d)) (inf_le_left.trans hd)) bv_imp_elim
  have hey := le_trans (le_inf (hU.trans (iInf_le _ e)) (inf_le_left.trans he)) bv_imp_elim
  exact bv_trans hdy (bv_symm hey)

/-- A set of pairs that is a function in the sense of `fnF` is a Flypitch function. -/
theorem fnB_le_is_function (D C f : bSet 𝔹) : fnB D C f ≤ is_function D C f := by
  set Γ := fnB D C f
  have hΓ : Γ ≤ fnB D C f := le_rfl
  have huniq : ∀ {Γ' : 𝔹} {a : bSet 𝔹}, Γ' ≤ Γ → Γ' ≤ a ∈ᴮ D →
      Γ' ≤ ⨆ y : bSet 𝔹, appB f a y ⊓ ⨅ y' : bSet 𝔹, appB f a y' ⟹ y' =ᴮ y :=
    fun hle ha => le_trans (le_inf ((hle.trans inf_le_right).trans (iInf_le _ _)) ha) bv_imp_elim
  refine le_inf (le_inf ?_ ?_) ?_
  · -- `is_func`
    refine le_iInf fun w₁ => le_iInf fun w₂ => le_iInf fun v₁ => le_iInf fun v₂ => ?_
    rw [← deduction, ← deduction]
    set Γ' := Γ ⊓ (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f) ⊓ w₁ =ᴮ w₂
    have hle : Γ' ≤ Γ := inf_le_left.trans inf_le_left
    have h1 : Γ' ≤ pair w₁ v₁ ∈ᴮ f := inf_le_left.trans (inf_le_right.trans inf_le_left)
    have h2 : Γ' ≤ pair w₂ v₂ ∈ᴮ f := inf_le_left.trans (inf_le_right.trans inf_le_right)
    have h2' : Γ' ≤ pair w₁ v₂ ∈ᴮ f :=
      bv_rw' (inf_le_right : Γ' ≤ w₁ =ᴮ w₂) (ϕ := fun w => pair w v₂ ∈ᴮ f)
        (h_congr := B_ext_pair_mem_left) (H_new := h2)
    have hw₁ : Γ' ≤ w₁ ∈ᴮ D := (fnB_mem (hle.trans hΓ) h1).trans inf_le_left
    exact uniq_of (huniq hle hw₁) h1 h2'
  · -- `is_total`
    refine le_iInf fun x => ?_
    rw [← deduction]
    have hu := huniq (Γ' := Γ ⊓ x ∈ᴮ D) inf_le_left inf_le_right
    refine le_trans (le_inf le_rfl hu) (le_trans (le_of_eq (inf_iSup_eq _ _))
      (iSup_mono fun y => ?_))
    have hxy : Γ ⊓ x ∈ᴮ D ⊓ (appB f x y ⊓ ⨅ y' : bSet 𝔹, appB f x y' ⟹ y' =ᴮ y) ≤
        pair x y ∈ᴮ f := inf_le_right.trans inf_le_left
    exact le_inf ((fnB_mem ((inf_le_left.trans inf_le_left).trans hΓ) hxy).trans inf_le_right) hxy
  · -- `f ⊆ D × C`
    rw [subset_unfold']
    refine le_iInf fun z => ?_
    rw [← deduction]
    have h := le_trans (le_inf ((inf_le_left.trans inf_le_left : Γ ⊓ z ∈ᴮ f ≤ _).trans
      (iInf_le _ z)) inf_le_right) bv_imp_elim
    refine h.trans (iSup_le fun x => ?_)
    rw [inf_iSup_eq]
    refine iSup_le fun y => ?_
    exact bv_rw' (inf_le_right.trans inf_le_right) (ϕ := fun w => w ∈ᴮ prod D C)
      (h_congr := B_ext_mem_left)
      (H_new := prod_mem inf_le_left (inf_le_right.trans inf_le_left))

/-- **(4) ω-sequences.** If the `ω`-sequences into `μ̌` in `V 𝔹` are exactly the
check of the ground set of `ω`-sequences (countable closure), and that ground
set injects into some `α ∈ k`, then `μ̌ ^ ℵ₀ < |ǩ|` holds in `V 𝔹`. -/
theorem powLtB_check {μ k α : PSet.{u}} (hα : α ∈ k)
    (hinj : PSet.injects_into (PSet.functions PSet.omega μ) α)
    (hF : (⊤ : 𝔹) ≤ check (PSet.functions PSet.omega μ) =ᴮ functions bSet.omega (check μ)) :
    (⊤ : 𝔹) ≤ powLtB (check μ) (check k) := by
  obtain ⟨h₀, hh₀⟩ := hinj
  have hcheck : (⊤ : 𝔹) ≤ is_injective_function (check (PSet.functions PSet.omega μ))
      (check α) (check h₀) := check_is_injective_function hh₀
  have htotal : (⊤ : 𝔹) ≤ is_total (check (PSet.functions PSet.omega μ)) (check α) (check h₀) :=
    ((hcheck.trans inf_le_left).trans inf_le_left).trans inf_le_right
  have hinj' : (⊤ : 𝔹) ≤ is_inj (check h₀) := hcheck.trans inf_le_right
  refine le_iSup_of_le (check α) (le_inf (check_mem hα) (le_iSup_of_le (check h₀) (le_inf ?_ ?_)))
  · refine le_iInf fun f => ?_
    rw [← deduction]
    have hfun : (⊤ : 𝔹) ⊓ fnB bSet.omega (check μ) f ≤ f ∈ᴮ functions bSet.omega (check μ) :=
      mem_functions_iff.mpr (inf_le_right.trans (fnB_le_is_function _ _ _))
    have hmem : (⊤ : 𝔹) ⊓ fnB bSet.omega (check μ) f ≤ f ∈ᴮ check (PSet.functions PSet.omega μ) :=
      subst_congr_mem_right' (bv_symm (le_top.trans hF)) hfun
    exact le_trans (le_inf ((le_top.trans htotal).trans (iInf_le _ f)) hmem) bv_imp_elim
  · refine le_iInf fun f => le_iInf fun f' => le_iInf fun b => ?_
    rw [← deduction, ← deduction, ← deduction, ← deduction]
    exact le_trans (le_inf (le_top.trans (hinj'.trans ((iInf_le _ f).trans ((iInf_le _ f').trans
      ((iInf_le _ b).trans (iInf_le _ b)))))) (le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      bv_refl)) bv_imp_elim

end Erdos1220Full.CardB

#print axioms Erdos1220Full.CardB.ordB_eq_Ord
#print axioms Erdos1220Full.CardB.leqB_check_eq_bot_of_chainCondition
#print axioms Erdos1220Full.CardB.cardinalB_card_ex_of_chainCondition
#print axioms Erdos1220Full.CardB.leqB_check_eq_bot_of_distrib
#print axioms Erdos1220Full.CardB.cardinalB_card_ex_of_distrib
#print axioms Erdos1220Full.CardB.cardinalB_card_ex_all
#print axioms Erdos1220Full.CardB.cofMapB_check_eq_bot
#print axioms Erdos1220Full.CardB.cofMapB_card_ex_eq_bot
#print axioms Erdos1220Full.CardB.injects_into_le_leqB
#print axioms Erdos1220Full.CardB.leqB_check_of_injects
#print axioms Erdos1220Full.CardB.cofinalB_check
#print axioms Erdos1220Full.CardB.fnB_le_is_function
#print axioms Erdos1220Full.CardB.powLtB_check
