import Erdos1220Full.HistoryForcingSmall
import Erdos1220.VertexDensity

/-!
# The historical forcing restricted to block-covering histories

Vertex density (`History.exists_pure_extension_mem`) needs every block to be
represented in the terminal condition. Covering is preserved by weak
extension (`WeakExtends.coversBlocks`), and the initial one-point-per-block
history covers, so we force with

  `CHP := {H : BPHistory // CoversBlocks H.1.last}`,  `q ≤ p :⇔ WeakExtends p q`,

shrunk to `CHP0 : Type u`, with completion `CAlg := RO CHP0 : Type u`.
Distributivity (from `strategic_closure`; all II positions purely extend a
covering start and all I moves weakly extend II positions, so everything
stays covering), reflection of small functions and the chain-condition hook
are transferred.
-/

open Cardinal Set Order Flypitch bSet Lattice

universe u w

namespace Erdos1220Full

namespace HistoryForcing

open Erdos1220 Erdos1220.BasicCondition Erdos1220.BPHistory

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-- Block-preserving histories whose terminal condition meets every block. -/
def CHP (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Type (u + 1) :=
  {H : BPHistory V I block μ hμ // CoversBlocks H.1.last}

instance instPreorderCHP : Preorder (CHP V I block μ hμ) where
  le p q := WeakExtends (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ) q.1 p.1
  le_refl p := WeakExtends.refl p.1
  le_trans _ _ _ hab hbc := hbc.trans hab

theorem CHP.le_iff {p q : CHP V I block μ hμ} : p ≤ q ↔ WeakExtends q.1 p.1 := Iff.rfl

instance small_CHP : Small.{u} (CHP V I block μ hμ) :=
  inferInstanceAs (Small.{u} {H : BPHistory V I block μ hμ // CoversBlocks H.1.last})

/-- The covering forcing as a `Type u` preorder. -/
def CHP0 (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Type u :=
  Shrink.{u} (CHP V I block μ hμ)

noncomputable def toCHP0 : CHP V I block μ hμ ≃ CHP0 V I block μ hμ :=
  equivShrink (CHP V I block μ hμ)

noncomputable instance instPreorderCHP0 : Preorder (CHP0 V I block μ hμ) :=
  Preorder.lift (toCHP0 (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ)).symm

theorem toCHP0_le_iff {a b : CHP V I block μ hμ} : toCHP0 a ≤ toCHP0 b ↔ a ≤ b := by
  show toCHP0.symm (toCHP0 a) ≤ toCHP0.symm (toCHP0 b) ↔ a ≤ b
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem CHP0.le_iff {a b : CHP0 V I block μ hμ} :
    a ≤ b ↔ WeakExtends (toCHP0.symm b).1 (toCHP0.symm a).1 := Iff.rfl

/-- The Boolean completion of the covering forcing, in `Type u`. -/
abbrev CAlg (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Type u :=
  RO (CHP0 V I block μ hμ)

/-- The underlying history of a condition. -/
noncomputable def CHP0.hist (q : CHP0 V I block μ hμ) : History V I block μ hμ :=
  (toCHP0.symm q).1.1

/-- The terminal basic condition of a condition. -/
noncomputable def CHP0.last (q : CHP0 V I block μ hμ) : BasicCondition V I block μ :=
  q.hist.last

theorem CHP0.blockPreserving (q : CHP0 V I block μ hμ) : q.hist.BlockPreserving :=
  (toCHP0.symm q).1.2

theorem CHP0.covers (q : CHP0 V I block μ hμ) : ∀ i : I, ∃ x ∈ q.last.support, block x = i :=
  (toCHP0.symm q).2

/-- Stronger conditions have extending terminal colourings. -/
theorem CHP0.last_extends {q r : CHP0 V I block μ hμ} (h : r ≤ q) :
    Extends q.last r.last :=
  WeakExtends.last_extends (CHP0.le_iff.mp h)

/-- Packing a covering history. -/
noncomputable def CHP0.mk (H : History V I block μ hμ) (hH : H.BlockPreserving)
    (hc : ∀ i : I, ∃ x ∈ H.last.support, block x = i) : CHP0 V I block μ hμ :=
  toCHP0 ⟨⟨H, hH⟩, hc⟩

theorem CHP0.mk_hist (H : History V I block μ hμ) (hH : H.BlockPreserving)
    (hc : ∀ i : I, ∃ x ∈ H.last.support, block x = i) : (CHP0.mk H hH hc).hist = H := by
  exact congrArg (fun y : CHP V I block μ hμ => y.1.1)
    (toCHP0.symm_apply_apply (⟨⟨H, hH⟩, hc⟩ : CHP V I block μ hμ))

/-- **Vertex density**: below any condition there is one whose terminal
support contains a given vertex. -/
theorem CHP0.exists_le_mem (q : CHP0 V I block μ hμ) (z : V) :
    ∃ r : CHP0 V I block μ hμ, r ≤ q ∧ z ∈ r.last.support := by
  obtain ⟨K, hpure, hbp, hz, hc⟩ :=
    History.exists_pure_extension_mem q.hist q.blockPreserving q.covers z
  refine ⟨CHP0.mk K hbp hc, ?_, ?_⟩
  · have hq : q = toCHP0 (toCHP0.symm q) := (Equiv.apply_symm_apply _ _).symm
    show toCHP0 (⟨⟨K, hbp⟩, hc⟩ : CHP V I block μ hμ) ≤ q
    rw [hq]
    exact toCHP0_le_iff.mpr (WeakExtends.of_pure hpure)
  · show z ∈ (CHP0.mk K hbp hc).hist.last.support
    rw [CHP0.mk_hist]
    exact hz

theorem nonemptyC [Nontrivial I] (rep : I → V) (hrep : ∀ i, block (rep i) = i)
    (hI : #I ≤ μ) : Nonempty (CHP0 V I block μ hμ) :=
  ⟨CHP0.mk (History.ofBlockSection (hμ := hμ) rep hrep hI)
    (History.ofBlockSection_blockPreserving rep hrep hI)
    (History.ofBlockSection_covers rep hrep hI)⟩

/-! ## Chain condition hook -/

theorem chainCondition_CAlg [Nonempty (CHP0 V I block μ hμ)] {θ : Cardinal.{u}}
    (h : ∀ (ι : Type u) (p : ι → CHP V I block μ hμ), θ ≤ #ι →
      ∃ i j, i ≠ j ∧ Compatible (p i) (p j)) :
    ChainCondition θ (CAlg V I block μ hμ) := by
  apply chainCondition_RO
  intro ι p hι
  obtain ⟨i, j, hij, ⟨r, hri, hrj⟩⟩ := h ι (fun k => toCHP0.symm (p k)) hι
  refine ⟨i, j, hij, toCHP0 r, ?_, ?_⟩
  · have := toCHP0_le_iff.mpr hri
    rwa [Equiv.apply_symm_apply] at this
  · have := toCHP0_le_iff.mpr hrj
    rwa [Equiv.apply_symm_apply] at this

/-! ## Distributivity -/

section Distributive

variable [Nonempty (CHP0 V I block μ hμ)]

theorem exists_forall_of_scheduleC {J : Type w} (e : J → Ordinal.{u})
    (he : Function.Injective e) {ρ : Ordinal.{u}} (hρ : ρ < (Order.succ μ).ord)
    (heρ : ∀ j, e j < ρ) {Γ : CAlg V I block μ hμ} (hΓ : ⊥ < Γ) {ι : J → Type*}
    (φ : ∀ j, ι j → CAlg V I block μ hμ)
    (hφ : ∀ j (Γ' : CAlg V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ j i) :
    ∃ (q : CHP0 V I block μ hμ) (c : ∀ j, ι j), emb q ≤ Γ ∧ ∀ j, emb q ≤ φ j (c j) := by
  classical
  obtain ⟨p₀, hp₀⟩ := exists_emb_le hΓ
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
      emb (T G) ≤ Γ → ∃ K : BPHistory V I block μ hμ, WeakExtends G K ∧
        ∃ i, emb (T K) ≤ φ j i := by
    intro j G hGc hG
    obtain ⟨i, hi⟩ := hφ j (emb (T G)) (emb_pos _) hG
    obtain ⟨r, hr⟩ := exists_emb_le hi
    obtain ⟨s, hsr, hsG⟩ := compatible_of_emb_le (hr.trans inf_le_left)
    have hKc : CoversBlocks (toCHP0.symm s).1.1.last := (toCHP0.symm s).2
    have hs : T (toCHP0.symm s).1 = s := by
      rw [hTeq _ hKc]
      exact Equiv.apply_symm_apply _ _
    refine ⟨(toCHP0.symm s).1, (hT _ _ hKc hGc).mp (by rw [hs]; exact hsG), i, ?_⟩
    rw [hs]
    exact (emb_mono hsr).trans (hr.trans inf_le_right)
  let Good : Ordinal.{u} → BPHistory V I block μ hμ → BPHistory V I block μ hμ → Prop :=
    fun α G K => WeakExtends G K ∧ ∀ j, e j = α → ∃ i, emb (T K) ≤ φ j i
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
  have hbelow : ∀ α, α < (Order.succ μ).ord → emb (T (play start moveI α)) ≤ Γ := by
    intro α hα
    have hle : T (play start moveI α) ≤ T start :=
      (hT _ _ (hcov α hα) hstartC).mpr (hstartW α hα)
    rw [hstart] at hle
    exact (emb_mono hle).trans hp₀
  have hmove : ∀ j, ∃ i, emb (T (moveI (e j) fun γ _ => play start moveI γ)) ≤ φ j i := by
    intro j
    have hlt : e j < (Order.succ μ).ord := (heρ j).trans hρ
    have hex : ∃ K, Good (e j) (play start moveI (e j)) K := by
      obtain ⟨K, hK, i, hi⟩ := hnext j _ (hcov _ hlt) (hbelow _ hlt)
      refine ⟨K, hK, fun j' hj' => ?_⟩
      obtain rfl := he hj'
      exact ⟨i, hi⟩
    have hm : (moveI (e j) fun γ _ => play start moveI γ) = Classical.choose hex := dif_pos hex
    rw [hm]
    exact (Classical.choose_spec hex).2 j rfl
  choose c hc using hmove
  refine ⟨T (play start moveI ρ), c, hbelow ρ hρ, fun j => ?_⟩
  have hmc : CoversBlocks (moveI (e j) fun γ _ => play start moveI γ).1.last :=
    (hmoveI (e j) fun γ _ => play start moveI γ).coversBlocks (hcov _ ((heρ j).trans hρ))
  exact (emb_mono ((hT _ _ (hcov ρ hρ) hmc).mpr (hweak (e j) ρ (heρ j) hρ))).trans (hc j)

/-- Distributivity for any index type of cardinality at most `μ`. -/
theorem exists_forall_of_card_leC {J : Type w}
    (hJ : Cardinal.lift.{u} #J ≤ Cardinal.lift.{w} μ)
    {Γ : CAlg V I block μ hμ} (hΓ : ⊥ < Γ) {ι : J → Type*}
    (φ : ∀ j, ι j → CAlg V I block μ hμ)
    (hφ : ∀ j (Γ' : CAlg V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ j i) :
    ∃ (q : CHP0 V I block μ hμ) (c : ∀ j, ι j), emb q ≤ Γ ∧ ∀ j, emb q ≤ φ j (c j) := by
  have hJ' : Cardinal.lift.{u} #J ≤ Cardinal.lift.{w} #(μ.ord.ToType) := by
    rwa [Cardinal.mk_toType, Cardinal.card_ord]
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hJ'
  let e : J → Ordinal.{u} := fun j => (Ordinal.ToType.mk.symm (f j)).1
  have he : Function.Injective e := by
    intro j k hjk
    exact f.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext hjk))
  exact exists_forall_of_scheduleC e he (Cardinal.ord_lt_ord.mpr (Order.lt_succ μ))
    (fun j => (Ordinal.ToType.mk.symm (f j)).2) hΓ φ hφ

/-- Distributivity for sequences indexed by the ordinals below `ρ < μ⁺`. -/
theorem exists_forall_ordinalC {ρ : Ordinal.{u}} (hρ : ρ < (Order.succ μ).ord)
    {Γ : CAlg V I block μ hμ} (hΓ : ⊥ < Γ) {ι : Ordinal.{u} → Type*}
    (φ : ∀ α, ι α → CAlg V I block μ hμ)
    (hφ : ∀ α, α < ρ → ∀ (Γ' : CAlg V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ →
      ∃ i, ⊥ < Γ' ⊓ φ α i) :
    ∃ (q : CHP0 V I block μ hμ) (c : ∀ α : Set.Iio ρ, ι α.1), emb q ≤ Γ ∧
      ∀ α : Set.Iio ρ, emb q ≤ φ α.1 (c α) :=
  exists_forall_of_scheduleC (J := Set.Iio ρ) Subtype.val Subtype.val_injective hρ
    (fun α => α.2) hΓ (fun α => φ α.1) (fun α => hφ α.1 α.2)

/-! ## No new small functions over `CAlg` -/

theorem reflect_function_CAlg {x y : PSet.{u}}
    (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j) (hxμ : #x.Type ≤ μ)
    {g : bSet (CAlg V I block μ hμ)} {Γ : CAlg V I block μ hμ} (hpos : ⊥ < Γ)
    (hfunc : Γ ≤ is_function (check x) (check y) g) :
    ∃ (f : PSet.{u}) (Δ : CAlg V I block μ hμ), ⊥ < Δ ∧ Δ ≤ Γ ∧
      Δ ≤ check f =ᴮ g ∧ PSet.is_func x y f := by
  have hsup : ∀ i : x.Type, Γ ≤ ⨆ j : (check y : bSet (CAlg V I block μ hμ)).type,
      pair (check (x.Func i)) (check (y.Func (check_cast j))) ∈ᴮ g := by
    intro i
    have htotal : Γ ≤ is_total (check x) (check y) g :=
      is_total_of_is_func' (is_func'_of_is_function hfunc)
    have hmem : Γ ≤ (check (x.Func i) : bSet (CAlg V I block μ hμ)) ∈ᴮ check x := by
      rw [check_mem'']
      exact le_top
    have hvalue : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check (x.Func i)) w ∈ᴮ g :=
      (le_inf (htotal.trans (iInf_le _ (check (x.Func i)))) hmem).trans bv_imp_elim
    rw [← @bounded_exists (CAlg V I block μ hμ) _ (check y)
      (fun w => pair (check (x.Func i)) w ∈ᴮ g)
      (h_congr := B_ext_pair_mem_right)] at hvalue
    simpa only [check_bval_top, top_inf_eq, check_func] using hvalue
  obtain ⟨q, c, hqΓ, hqc⟩ := exists_forall_of_card_leC (Cardinal.lift_le.mpr hxμ) hpos
    (ι := fun _ => (check y : bSet (CAlg V I block μ hμ)).type)
    (fun i j => pair (check (x.Func i)) (check (y.Func (check_cast j))) ∈ᴮ g)
    (fun i Γ' hΓ' hle => nonzero_inf_of_nonzero_le_supr hΓ' (hle.trans (hsup i)))
  obtain ⟨f, hf, hfis⟩ := check_eq_of_forall_pair_general hx (fun i => check_cast (c i))
    (hqΓ.trans hfunc) hqc
  exact ⟨f, emb q, emb_pos q, hqΓ, hf, hfis⟩

theorem check_functions_eq_CAlg {x y : PSet.{u}}
    (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j) (hxμ : #x.Type ≤ μ)
    (Γ : CAlg V I block μ hμ) :
    Γ ≤ check (PSet.functions x y) =ᴮ functions (check x) (check y) := by
  refine subset_ext check_functions_subset_functions ?_
  rw [subset_unfold']
  apply le_iInf
  intro g
  rw [← deduction]
  apply le_of_positive_refinements
  intro Δ hpos hΔ
  have hfunc : Δ ≤ is_function (check x) (check y) g :=
    mem_functions_iff.mp (hΔ.trans inf_le_right)
  obtain ⟨f, Δ', hpos', hle, heq, hf⟩ := reflect_function_CAlg hx hxμ hpos hfunc
  refine ⟨Δ', hpos', hle, ?_⟩
  exact bv_rw' (bv_symm heq)
    (ϕ := fun z => z ∈ᴮ check (PSet.functions x y))
    (h_congr := B_ext_mem_left)
    (H_new := check_mem ((PSet.mem_functions_iff f).mpr hf))

end Distributive

end HistoryForcing

end Erdos1220Full

#print axioms Erdos1220Full.HistoryForcing.small_CHP
#print axioms Erdos1220Full.HistoryForcing.toCHP0_le_iff
#print axioms Erdos1220Full.HistoryForcing.CHP0.exists_le_mem
#print axioms Erdos1220Full.HistoryForcing.CHP0.last_extends
#print axioms Erdos1220Full.HistoryForcing.nonemptyC
#print axioms Erdos1220Full.HistoryForcing.chainCondition_CAlg
#print axioms Erdos1220Full.HistoryForcing.exists_forall_of_scheduleC
#print axioms Erdos1220Full.HistoryForcing.exists_forall_of_card_leC
#print axioms Erdos1220Full.HistoryForcing.exists_forall_ordinalC
#print axioms Erdos1220Full.HistoryForcing.reflect_function_CAlg
#print axioms Erdos1220Full.HistoryForcing.check_functions_eq_CAlg
