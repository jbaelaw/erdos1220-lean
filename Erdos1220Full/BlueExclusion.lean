import Erdos1220Full.GenericColouring
import Erdos1220Full.CardPreserveSem
import Erdos1220.CliqueCountable

/-!
# No uncountable blue-homogeneous set in the generic colouring

For the covering historical forcing `CAlg` and the generic colouring `cdot`
on `check x`, the second disjunct of `Sem.arrow` has Boolean value `⊥`:
no ordinal `w` which is `ω₁` in `V 𝔹` admits `H ⊆ x̌` with `|H| = |w|` and `H`
blue-homogeneous. Assumes `ℵ₁ ≤ μ` and that `x` is well behaved (distinct
elements are non-equivalent and `∈`-comparable, e.g. `x` an ordinal).

Proof: `ω̌₁ ⊆ ℵ₁^{V𝔹} ⊆ w`; an injection `f : w → H` is decided on `ω̌₁` by one
condition via strategic closure (`exists_forall_dense`), giving an injective
ground map `g0 : ω₁ → x`; a second application decides all `ℵ₁ × ℵ₁` colours
blue in one condition, whose terminal blue clique `range g0` is then
uncountable, contradicting `BlockPreserving.blue_clique_countable`.
-/

open Cardinal Set Order Flypitch bSet Lattice

universe u

namespace Erdos1220Full

namespace HistoryForcing

open Erdos1220 Erdos1220.BasicCondition Erdos1220.BPHistory

section Dense

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- **Meeting `μ` downward closed dense sets.** Strategic closure of the
history order, stated inside the preorder `CHP0`. -/
theorem exists_forall_dense [Nonempty (CHP0 V I block μ hμ)] {J : Type u} (hJ : #J ≤ μ)
    (p₀ : CHP0 V I block μ hμ) (D : J → CHP0 V I block μ hμ → Prop)
    (hmono : ∀ j q r, r ≤ q → D j q → D j r)
    (hdense : ∀ j p, p ≤ p₀ → ∃ r, r ≤ p ∧ D j r) :
    ∃ q, q ≤ p₀ ∧ ∀ j, D j q := by
  classical
  have hJ' : Cardinal.lift.{u} #J ≤ Cardinal.lift.{u} #(μ.ord.ToType) := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]; exact Cardinal.lift_le.mpr hJ
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hJ'
  let e : J → Ordinal.{u} := fun j => (Ordinal.ToType.mk.symm (f j)).1
  have he : Function.Injective e := by
    intro j k hjk
    exact f.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext hjk))
  have heρ : ∀ j, e j < μ.ord := fun j => (Ordinal.ToType.mk.symm (f j)).2
  have hρ : μ.ord < (Order.succ μ).ord := Cardinal.ord_lt_ord.mpr (Order.lt_succ μ)
  let T : BPHistory V I block μ hμ → CHP0 V I block μ hμ := fun K =>
    if h : CoversBlocks K.1.last then toCHP0 ⟨K, h⟩ else p₀
  have hTeq : ∀ K (h : CoversBlocks K.1.last), T K = toCHP0 ⟨K, h⟩ := fun K h => dif_pos h
  have hT : ∀ a b (ha : CoversBlocks a.1.last) (hb : CoversBlocks b.1.last),
      T a ≤ T b ↔ WeakExtends b a := by
    intro a b ha hb
    rw [hTeq a ha, hTeq b hb]
    exact toCHP0_le_iff
  let start : BPHistory V I block μ hμ := (toCHP0.symm p₀).1
  have hstartC : CoversBlocks start.1.last := (toCHP0.symm p₀).2
  have hstart : T start = p₀ := by
    rw [hTeq start hstartC]
    exact Equiv.apply_symm_apply _ _
  have hnext : ∀ (j : J) (G : BPHistory V I block μ hμ), CoversBlocks G.1.last →
      T G ≤ p₀ → ∃ K : BPHistory V I block μ hμ, WeakExtends G K ∧ D j (T K) := by
    intro j G hGc hG
    obtain ⟨r, hr, hD⟩ := hdense j (T G) hG
    have hKc : CoversBlocks (toCHP0.symm r).1.1.last := (toCHP0.symm r).2
    have hs : T (toCHP0.symm r).1 = r := by
      rw [hTeq _ hKc]
      exact Equiv.apply_symm_apply _ _
    refine ⟨(toCHP0.symm r).1, (hT _ _ hKc hGc).mp (by rw [hs]; exact hr), ?_⟩
    rw [hs]
    exact hD
  let Good : Ordinal.{u} → BPHistory V I block μ hμ → BPHistory V I block μ hμ → Prop :=
    fun α G K => WeakExtends G K ∧ ∀ j, e j = α → D j (T K)
  let moveI : ∀ α : Ordinal.{u}, (∀ γ, γ ≤ α → BPHistory V I block μ hμ) →
      BPHistory V I block μ hμ := fun α past =>
    if h : ∃ K, Good α (past α le_rfl) K then Classical.choose h else past α le_rfl
  have hmoveI : ∀ α past, WeakExtends (past α le_rfl) (moveI α past) := by
    intro α past
    by_cases h : ∃ K, Good α (past α le_rfl) K
    · have hm : moveI α past = Classical.choose h := dif_pos h
      rw [hm]
      exact (Classical.choose_spec h).1
    · have hm : moveI α past = past α le_rfl := dif_neg h
      rw [hm]
      exact WeakExtends.refl _
  obtain ⟨h0, hchain, -, hweak⟩ := strategic_closure start moveI hmoveI
  have hstartW : ∀ α, α < (Order.succ μ).ord → WeakExtends start (play start moveI α) := by
    intro α hα
    have hpure := hchain 0 α bot_le hα
    rw [h0] at hpure
    exact WeakExtends.of_pure hpure
  have hcov : ∀ α, α < (Order.succ μ).ord → CoversBlocks (play start moveI α).1.last :=
    fun α hα => (hstartW α hα).coversBlocks hstartC
  have hbelow : ∀ α, α < (Order.succ μ).ord → T (play start moveI α) ≤ p₀ := by
    intro α hα
    have hle : T (play start moveI α) ≤ T start :=
      (hT _ _ (hcov α hα) hstartC).mpr (hstartW α hα)
    rwa [hstart] at hle
  have hmove : ∀ j, D j (T (moveI (e j) fun γ _ => play start moveI γ)) := by
    intro j
    have hlt : e j < (Order.succ μ).ord := (heρ j).trans hρ
    have hex : ∃ K, Good (e j) (play start moveI (e j)) K := by
      obtain ⟨K, hK, hD⟩ := hnext j _ (hcov _ hlt) (hbelow _ hlt)
      refine ⟨K, hK, fun j' hj' => ?_⟩
      obtain rfl := he hj'
      exact hD
    have hm : (moveI (e j) fun γ _ => play start moveI γ) = Classical.choose hex := dif_pos hex
    rw [hm]
    exact (Classical.choose_spec hex).2 j rfl
  refine ⟨T (play start moveI μ.ord), hbelow _ hρ, fun j => ?_⟩
  have hmc : CoversBlocks (moveI (e j) fun γ _ => play start moveI γ).1.last :=
    (hmoveI (e j) fun γ _ => play start moveI γ).coversBlocks (hcov _ ((heρ j).trans hρ))
  exact hmono j _ _ ((hT _ _ (hcov _ hρ) hmc).mpr (hweak (e j) _ (heρ j) hρ)) (hmove j)

end Dense

end HistoryForcing

namespace GenericColouring

open Erdos1220 Erdos1220.BasicCondition HistoryForcing
open Flypitch.Erdos1220

variable {I : Type} {x : PSet.{0}} {block : x.Type → I} {μ : Cardinal.{0}} {hμ : ℵ₀ ≤ μ}

theorem Decides.symm {q : CHP0 x.Type I block μ hμ} {a b : x.Type} {c : Bool}
    (h : Decides x block μ hμ q a b c) : Decides x block μ hμ q b a c :=
  ⟨h.2.1, h.1, ⟨fun hb => h.2.2.mp (q.last.symmetric hb),
    fun hc => q.last.symmetric (h.2.2.mpr hc)⟩⟩

variable [Nonempty (CHP0 x.Type I block μ hμ)]

/-- `ω̌₁ ⊆ w` for any `w` which is `ω₁` in `V 𝔹`. -/
theorem check_aleph_one_subset_of_omega1 {Γ : CAlg x.Type I block μ hμ}
    {w : bSet (CAlg x.Type I block μ hμ)} (h : Γ ≤ Sem.omega1 w) :
    Γ ≤ (check (PSet.card_ex (Cardinal.aleph 1)) : bSet (CAlg x.Type I block μ hμ)) ⊆ᴮ w := by
  have hOrd : Γ ≤ Ord w := by
    have h1 : Γ ≤ CardB.ordB w := h.trans inf_le_left
    rwa [CardB.ordB_eq_Ord] at h1
  have hninj : Γ ≤ (injects_into w bSet.omega)ᶜ :=
    (h.trans (inf_le_right.trans inf_le_left)).trans
      (compl_le_compl (CardB.injects_into_le_leqB w bSet.omega))
  have hspec := bSet.aleph_one_satisfies_spec (𝔹 := CAlg x.Type I block μ hμ) (Γ := Γ)
  have hsub : Γ ≤ bSet.aleph_one ⊆ᴮ w :=
    bv_context_apply (bv_context_apply
      ((hspec.trans (inf_le_right.trans inf_le_right)).trans (iInf_le _ w)) hOrd) hninj
  exact subset_trans' bSet.aleph_one_check_sub_aleph_one hsub

/-- A blue decision for an `∈`-ordered pair of members of a blue-homogeneous `H`. -/
theorem exists_le_decides_blue (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    {H : bSet (CAlg x.Type I block μ hμ)} {v v' : x.Type} (hvv' : x.Func v ∈ x.Func v')
    (p : CHP0 x.Type I block μ hμ)
    (hv : emb p ≤ check (x.Func v) ∈ᴮ H) (hv' : emb p ≤ check (x.Func v') ∈ᴮ H)
    (hh : emb p ≤ Sem.homog1 (cdot x block μ hμ) H) :
    ∃ r, r ≤ p ∧ Decides x block μ hμ r v v' true := by
  have hcol := colouring_cdot (x := x) (block := block) (μ := μ) (hμ := hμ) hx
  unfold Sem.colouring at hcol
  unfold Sem.homog1 at hh
  have hm : emb p ≤ (check (x.Func v) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ check x := by
    rw [check_mem'']; exact le_top
  have hm' : emb p ≤ (check (x.Func v') : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ check x := by
    rw [check_mem'']; exact le_top
  have hvm : emb p ≤ (check (x.Func v) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ
      check (x.Func v') := check_mem hvv'
  have c1 := bv_context_apply ((le_top.trans hcol).trans (iInf_le _ (check (x.Func v)))) hm
  have c2 := bv_context_apply (c1.trans (iInf_le _ (check (x.Func v')))) hm'
  have c3 := bv_context_apply c2 hvm
  have h1 := bv_context_apply (hh.trans (iInf_le _ (check (x.Func v)))) hv
  have h2 := bv_context_apply (h1.trans (iInf_le _ (check (x.Func v')))) hv'
  have h3 := bv_context_apply h2 hvm
  obtain ⟨i, hi⟩ := nonzero_inf_of_nonzero_le_supr (emb_pos p) c3
  set Γ' := emb p ⊓ (Flypitch.Erdos501.Sem.app (cdot x block μ hμ)
      (pair (check (x.Func v)) (check (x.Func v'))) i ⊓ ((Sem.zero i ⊔ Sem.one i) ⊓
        ⨅ i', Flypitch.Erdos501.Sem.app (cdot x block μ hμ)
          (pair (check (x.Func v)) (check (x.Func v'))) i' ⟹ i' =ᴮ i)) with hΓ'def
  have happ : Γ' ≤ Flypitch.Erdos501.Sem.app (cdot x block μ hμ)
        (pair (check (x.Func v)) (check (x.Func v'))) i := inf_le_right.trans inf_le_left
  have hone := bv_context_apply ((inf_le_left.trans h3).trans (iInf_le _ i)) happ
  obtain ⟨q, hq, ha, hb, hbl⟩ := exists_blue_of_app_one hx happ hone hi le_rfl
  obtain ⟨s, hsq, hsp⟩ := compatible_of_emb_le (hq.trans inf_le_left)
  exact ⟨s, hsp, Decides.mono ⟨ha, hb, iff_of_true hbl rfl⟩ hsq⟩

/-- **The blue half of the partition relation fails.** -/
theorem omega1_homog_le_bot (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    (hxord : ∀ i j, i ≠ j → x.Func i ∈ x.Func j ∨ x.Func j ∈ x.Func i)
    (hμ1 : Cardinal.aleph 1 ≤ μ) (w H : bSet (CAlg x.Type I block μ hμ)) :
    Sem.omega1 w ⊓ (Sem.subset H (check x) ⊓
      (Sem.eqCard H w ⊓ Sem.homog1 (cdot x block μ hμ) H)) ≤ ⊥ := by
  classical
  set E := Sem.omega1 w ⊓ (Sem.subset H (check x) ⊓
      (Sem.eqCard H w ⊓ Sem.homog1 (cdot x block μ hμ) H)) with hEdef
  by_contra hne
  have hE : ⊥ < E := bot_lt_iff_not_le_bot.mpr hne
  let K : PSet.{0} := PSet.card_ex (Cardinal.aleph 1)
  have hKcard : #K.Type = Cardinal.aleph 1 :=
    PSet.mk_type_mk_eq (Cardinal.aleph 1) (Cardinal.aleph0_le_aleph 1)
  have hω : E ≤ Sem.omega1 w := inf_le_left
  have hsubH : E ≤ Sem.subset H (check x) := inf_le_right.trans inf_le_left
  have hleq : E ≤ CardB.leqB w H :=
    inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hhom : E ≤ Sem.homog1 (cdot x block μ hμ) H :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  have hKw : E ≤ (check K : bSet (CAlg x.Type I block μ hμ)) ⊆ᴮ w :=
    check_aleph_one_subset_of_omega1 hω
  unfold CardB.leqB at hleq
  obtain ⟨f, hf⟩ := nonzero_inf_of_nonzero_le_supr hE hleq
  set Δ1 := E ⊓ (CardB.isFunB w H f ⊓ CardB.injOnB w f) with hΔ1def
  have hfun : Δ1 ≤ CardB.isFunB w H f := inf_le_right.trans inf_le_left
  have hinj : Δ1 ≤ CardB.injOnB w f := inf_le_right.trans inf_le_right
  have hΔ1E : Δ1 ≤ E := inf_le_left
  unfold CardB.isFunB at hfun
  unfold CardB.injOnB at hinj
  have hmemw : ∀ a : K.Type, Δ1 ≤ (check (K.Func a) : bSet (CAlg x.Type I block μ hμ)) ∈ᴮ w :=
    fun a => mem_of_mem_subset (hΔ1E.trans hKw) (by rw [check_mem'']; exact le_top)
  obtain ⟨p₀, hp₀⟩ := exists_emb_le hf
  -- Stage 1: decide the injection on `ω̌₁`.
  let D1 : K.Type → CHP0 x.Type I block μ hμ → Prop := fun a q => ∃ v : x.Type,
    emb q ≤ CardB.appB f (check (K.Func a)) (check (x.Func v)) ⊓ check (x.Func v) ∈ᴮ H
  have hD1mono : ∀ a q r, r ≤ q → D1 a q → D1 a r := by
    rintro a q r hrq ⟨v, hv⟩
    exact ⟨v, (emb_mono hrq).trans hv⟩
  have hD1dense : ∀ a p, p ≤ p₀ → ∃ r, r ≤ p ∧ D1 a r := by
    intro a p hp
    have hpΔ : emb p ≤ Δ1 := (emb_mono hp).trans hp₀
    have htot := bv_context_apply ((hpΔ.trans hfun).trans (iInf_le _ (check (K.Func a))))
      (hpΔ.trans (hmemw a))
    obtain ⟨y, hy⟩ := nonzero_inf_of_nonzero_le_supr (emb_pos p) htot
    set Γ1 := emb p ⊓ (y ∈ᴮ H ⊓ (CardB.appB f (check (K.Func a)) y ⊓
      ⨅ y', CardB.appB f (check (K.Func a)) y' ⟹ y' =ᴮ y)) with hΓ1def
    have hyH : Γ1 ≤ y ∈ᴮ H := inf_le_right.trans inf_le_left
    have hyapp : Γ1 ≤ CardB.appB f (check (K.Func a)) y :=
      inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hyl := bv_context_apply
      ((inf_le_left.trans (hpΔ.trans (hΔ1E.trans hsubH))).trans (iInf_le _ y)) hyH
    obtain ⟨v, Γ2, hΓ2, hΓ2le, hyv⟩ := eq_check_of_mem_check hy hyl
    have happ : Γ2 ≤ CardB.appB f (check (K.Func a)) (check (x.Func v)) :=
      bv_rw' (bv_symm hyv) (ϕ := fun z => pair (check (K.Func a)) z ∈ᴮ f)
        (h_congr := B_ext_pair_mem_right) (H_new := hΓ2le.trans hyapp)
    have hvH : Γ2 ≤ check (x.Func v) ∈ᴮ H :=
      bv_rw' (bv_symm hyv) (ϕ := fun z => z ∈ᴮ H) (h_congr := B_ext_mem_left)
        (H_new := hΓ2le.trans hyH)
    obtain ⟨r, hr⟩ := exists_emb_le hΓ2
    obtain ⟨s, hsr, hsp⟩ := compatible_of_emb_le (hr.trans (hΓ2le.trans inf_le_left))
    exact ⟨s, hsp, v, (emb_mono hsr).trans (hr.trans (le_inf happ hvH))⟩
  obtain ⟨q₁, hq₁, hD1⟩ := exists_forall_dense (by rw [hKcard]; exact hμ1) p₀ D1 hD1mono hD1dense
  choose g0 hg0 using hD1
  have hq₁Δ : emb q₁ ≤ Δ1 := (emb_mono hq₁).trans hp₀
  have hg0inj : Function.Injective g0 := by
    intro a b hab
    by_contra hab'
    have h1 : emb q₁ ≤ CardB.appB f (check (K.Func a)) (check (x.Func (g0 a))) :=
      (hg0 a).trans inf_le_left
    have h2 : emb q₁ ≤ CardB.appB f (check (K.Func b)) (check (x.Func (g0 a))) := by
      rw [hab]; exact (hg0 b).trans inf_le_left
    have s1 := bv_context_apply ((hq₁Δ.trans hinj).trans (iInf_le _ (check (K.Func a))))
      (hq₁Δ.trans (hmemw a))
    have s2 := bv_context_apply (s1.trans (iInf_le _ (check (K.Func b)))) (hq₁Δ.trans (hmemw b))
    have s3 := bv_context_apply (bv_context_apply
      (s2.trans (iInf_le _ (check (x.Func (g0 a))))) h1) h2
    rw [check_bv_eq_bot_of_not_equiv (CardB.card_ex_inj _ a b hab')] at s3
    exact (not_le_of_gt (emb_pos q₁)) s3
  -- Stage 2: decide all colours blue.
  let J2 := {ab : K.Type × K.Type // ab.1 ≠ ab.2}
  have hJ2 : #J2 ≤ μ := by
    refine (Cardinal.mk_subtype_le _).trans ?_
    rw [Cardinal.mk_prod, Cardinal.lift_id, hKcard,
      Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)]
    exact hμ1
  let D2 : J2 → CHP0 x.Type I block μ hμ → Prop := fun ab q =>
    Decides x block μ hμ q (g0 ab.1.1) (g0 ab.1.2) true
  have hD2mono : ∀ ab q r, r ≤ q → D2 ab q → D2 ab r :=
    fun ab q r hrq h => Decides.mono h hrq
  have hD2dense : ∀ ab p, p ≤ q₁ → ∃ r, r ≤ p ∧ D2 ab r := by
    rintro ⟨⟨a, b⟩, hab⟩ p hp
    have hpq : emb p ≤ emb q₁ := emb_mono hp
    have hva : emb p ≤ check (x.Func (g0 a)) ∈ᴮ H := hpq.trans ((hg0 a).trans inf_le_right)
    have hvb : emb p ≤ check (x.Func (g0 b)) ∈ᴮ H := hpq.trans ((hg0 b).trans inf_le_right)
    have hh : emb p ≤ Sem.homog1 (cdot x block μ hμ) H := hpq.trans (hq₁Δ.trans (hΔ1E.trans hhom))
    rcases hxord (g0 a) (g0 b) (fun h => hab (hg0inj h)) with hlt | hlt
    · exact exists_le_decides_blue hx hlt p hva hvb hh
    · obtain ⟨r, hr, hd⟩ := exists_le_decides_blue hx hlt p hvb hva hh
      exact ⟨r, hr, hd.symm⟩
  obtain ⟨q₂, hq₂, hD2⟩ := exists_forall_dense hJ2 q₁ D2 hD2mono hD2dense
  -- The terminal blue clique is uncountable.
  have hnt : Nontrivial K.Type := by
    rw [← Cardinal.one_lt_iff_nontrivial, hKcard]
    exact Cardinal.one_lt_aleph0.trans_le (Cardinal.aleph0_le_aleph 1)
  have hCsupp : Set.range g0 ⊆ q₂.hist.last.support := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := exists_ne a
    exact (hD2 ⟨(a, b), hb.symm⟩).1
  have hCblue : ∀ y ∈ Set.range g0, ∀ z ∈ Set.range g0, y ≠ z → q₂.hist.last.blue y z := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne'
    have hab : a ≠ b := fun h => hne' (congrArg g0 h)
    exact (hD2 ⟨(a, b), hab⟩).2.2.mpr rfl
  have hle := History.BlockPreserving.blue_clique_cardinal_le_aleph0 q₂.blockPreserving
    (Set.range g0) hCsupp hCblue
  rw [Cardinal.mk_range_eq g0 hg0inj, hKcard] at hle
  exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hle

/-- **`Γ ⊓ (second disjunct of Sem.arrow) ≤ ⊥`** for the generic colouring. -/
theorem blue_disjunct_le_bot (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    (hxord : ∀ i j, i ≠ j → x.Func i ∈ x.Func j ∨ x.Func j ∈ x.Func i)
    (hμ1 : Cardinal.aleph 1 ≤ μ) :
    (⊤ : CAlg x.Type I block μ hμ) ⊓
      (⨆ w : bSet (CAlg x.Type I block μ hμ), Sem.omega1 w ⊓
        ⨆ H : bSet (CAlg x.Type I block μ hμ), Sem.subset H (check x) ⊓
          (Sem.eqCard H w ⊓ Sem.homog1 (cdot x block μ hμ) H)) ≤ ⊥ := by
  rw [top_inf_eq]
  apply iSup_le
  intro w
  rw [inf_iSup_eq]
  apply iSup_le
  intro H
  exact omega1_homog_le_bot hx hxord hμ1 w H

end GenericColouring

end Erdos1220Full

#print axioms Erdos1220Full.HistoryForcing.exists_forall_dense
#print axioms Erdos1220Full.GenericColouring.check_aleph_one_subset_of_omega1
#print axioms Erdos1220Full.GenericColouring.exists_le_decides_blue
#print axioms Erdos1220Full.GenericColouring.omega1_homog_le_bot
#print axioms Erdos1220Full.GenericColouring.blue_disjunct_le_bot
