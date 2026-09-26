import Erdos1220Full.HistoryForcing

/-!
# The historical forcing, shrunk to `Type u`

Flypitch's `V 𝔹` needs the Boolean algebra in the same universe as the
pre-sets. Histories live in `Type (u + 1)` (their lengths are ordinals), but
there are only `u`-small many of them: a history is determined by its length
below `(succ μ).ord`, its states and its transition witnesses, all of which
can be coded by functions on `Iio (succ μ).ord` with values in `Type u`.

So `HP0 := Shrink.{u} (HP …)`, with the transferred preorder, is
order-isomorphic to `HP` and `Alg0 := RO HP0 : Type u`. With `u = 0` this is an
algebra in `Type`. We transfer nonemptiness, distributivity, reflection of
small functions, and the chain-condition hook.
-/

open Cardinal Set Order Flypitch bSet Lattice

universe u w

namespace Erdos1220Full

namespace HistoryForcing

open Erdos1220 Erdos1220.BasicCondition Erdos1220.BPHistory

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-! ## Smallness of histories -/

/-- Indices below the length bound. -/
abbrev Bound (μ : Cardinal.{u}) : Type (u + 1) := Set.Iio (Order.succ μ).ord

/-- A transition witness packaged with its endpoints. -/
abbrev StepData (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Type u :=
  Σ pr : BasicCondition V I block μ × BasicCondition V I block μ, Transition hμ pr.1 pr.2

open Classical in
/-- A non-dependent code of a history. -/
noncomputable def code (H : History V I block μ hμ) :
    Bound μ × (Bound μ → Option (BasicCondition V I block μ)) ×
      (Bound μ → Option (StepData V I block μ hμ)) :=
  (⟨H.length, H.length_lt⟩,
    fun i => if h : i.1 ≤ H.length then some (H.state i.1 h) else none,
    fun i => if h : Order.succ i.1 ≤ H.length then
      some ⟨(H.state i.1 ((Order.le_succ _).trans h), H.state (Order.succ i.1) h),
        H.step i.1 h⟩ else none)

theorem code_injective :
    Function.Injective (code (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ)) := by
  intro H K hHK
  have hl : H.length = K.length := congrArg (fun c => c.1.1) hHK
  have hs := congrArg (fun c => c.2.1) hHK
  have hst := congrArg (fun c => c.2.2) hHK
  apply History.ext_of hl
  · intro i hi hk
    have h := congrFun hs ⟨i, hi.trans_lt H.length_lt⟩
    dsimp only [code] at h
    rw [dif_pos hi, dif_pos hk] at h
    exact Option.some.inj h
  · intro i hi hk
    have h := congrFun hst ⟨i, ((Order.lt_succ i).trans_le hi).trans H.length_lt⟩
    dsimp only [code] at h
    rw [dif_pos hi, dif_pos hk] at h
    exact (Sigma.mk.inj_iff.mp (Option.some.inj h)).2

instance small_history : Small.{u} (History V I block μ hμ) :=
  small_of_injective code_injective

instance small_bpHistory : Small.{u} (BPHistory V I block μ hμ) :=
  small_subtype _ _

instance small_HP : Small.{u} (HP V I block μ hμ) :=
  inferInstanceAs (Small.{u} (BPHistory V I block μ hμ))

/-! ## The shrunk forcing -/

/-- The historical forcing as a `Type u` preorder. -/
def HP0 (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Type u :=
  Shrink.{u} (HP V I block μ hμ)

/-- The identification `HP ≃ HP0`. -/
noncomputable def toHP0 : HP V I block μ hμ ≃ HP0 V I block μ hμ :=
  equivShrink (HP V I block μ hμ)

noncomputable instance instPreorderHP0 : Preorder (HP0 V I block μ hμ) :=
  Preorder.lift (toHP0 (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ)).symm

theorem toHP0_le_iff {a b : HP V I block μ hμ} : toHP0 a ≤ toHP0 b ↔ a ≤ b := by
  show toHP0.symm (toHP0 a) ≤ toHP0.symm (toHP0 b) ↔ a ≤ b
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem toHP0_le_iff_weak {a b : BPHistory V I block μ hμ} :
    toHP0 (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ) a ≤ toHP0 b ↔
      WeakExtends b a :=
  toHP0_le_iff

theorem le_iff_symm {a b : HP0 V I block μ hμ} : a ≤ b ↔ toHP0.symm a ≤ toHP0.symm b :=
  Iff.rfl

/-- The Boolean completion, in `Type u`. -/
abbrev Alg0 (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Type u :=
  RO (HP0 V I block μ hμ)

theorem nonempty_HP0 [h : Nonempty (HP V I block μ hμ)] : Nonempty (HP0 V I block μ hμ) :=
  ⟨toHP0 h.some⟩

theorem nonempty0 [Nontrivial I] (rep : I → V) (hrep : ∀ i, block (rep i) = i)
    (hI : #I ≤ μ) : Nonempty (HP0 V I block μ hμ) :=
  haveI := nonempty (hμ := hμ) rep hrep hI
  nonempty_HP0

/-! ## Chain condition hook -/

theorem compatible_toHP0 {a b : HP V I block μ hμ} (h : Compatible a b) :
    Compatible (toHP0 a) (toHP0 b) := by
  obtain ⟨r, hra, hrb⟩ := h
  exact ⟨toHP0 r, toHP0_le_iff.mpr hra, toHP0_le_iff.mpr hrb⟩

/-- Antichains of the history order, indexed by `u`-small types, bounded by
`θ` give the `θ`-chain condition of `Alg0`. -/
theorem chainCondition_Alg0 [Nonempty (HP0 V I block μ hμ)] {θ : Cardinal.{u}}
    (h : ∀ (ι : Type u) (p : ι → HP V I block μ hμ), θ ≤ #ι →
      ∃ i j, i ≠ j ∧ Compatible (p i) (p j)) :
    ChainCondition θ (Alg0 V I block μ hμ) := by
  apply chainCondition_RO
  intro ι p hι
  obtain ⟨i, j, hij, hc⟩ := h ι (fun k => toHP0.symm (p k)) hι
  refine ⟨i, j, hij, ?_⟩
  have := compatible_toHP0 hc
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this

/-- The same hook from `AntichainBound` on the large preorder. -/
theorem chainCondition_Alg0_of_antichainBound [Nonempty (HP0 V I block μ hμ)]
    {θ : Cardinal.{u}} (h : AntichainBound (Cardinal.lift.{u + 1} θ) (HP V I block μ hμ)) :
    ChainCondition θ (Alg0 V I block μ hμ) := by
  apply chainCondition_Alg0
  intro ι p hι
  obtain ⟨i, j, hij, hc⟩ := h (ULift.{u + 1} ι) (fun k => p k.down)
    (by rw [Cardinal.mk_uLift]; exact Cardinal.lift_le.mpr hι)
  exact ⟨i.down, j.down, fun he => hij (ULift.down_injective he), hc⟩

/-! ## Distributivity for the shrunk forcing -/

section Distributive

variable [Nonempty (HP0 V I block μ hμ)]

theorem exists_forall_of_schedule0 {J : Type w} (e : J → Ordinal.{u})
    (he : Function.Injective e) {ρ : Ordinal.{u}} (hρ : ρ < (Order.succ μ).ord)
    (heρ : ∀ j, e j < ρ) {Γ : Alg0 V I block μ hμ} (hΓ : ⊥ < Γ) {ι : J → Type*}
    (φ : ∀ j, ι j → Alg0 V I block μ hμ)
    (hφ : ∀ j (Γ' : Alg0 V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ j i) :
    ∃ (q : HP0 V I block μ hμ) (c : ∀ j, ι j), emb q ≤ Γ ∧ ∀ j, emb q ≤ φ j (c j) := by
  classical
  let T : BPHistory V I block μ hμ → HP0 V I block μ hμ := fun K => toHP0 K
  have hT : ∀ a b : BPHistory V I block μ hμ, T a ≤ T b ↔ WeakExtends b a :=
    fun a b => toHP0_le_iff
  obtain ⟨p₀, hp₀⟩ := exists_emb_le hΓ
  let start : BPHistory V I block μ hμ := toHP0.symm p₀
  have hstart : T start = p₀ := Equiv.apply_symm_apply _ _
  have hnext : ∀ (j : J) (G : BPHistory V I block μ hμ), emb (T G) ≤ Γ →
      ∃ K : BPHistory V I block μ hμ, WeakExtends G K ∧ ∃ i, emb (T K) ≤ φ j i := by
    intro j G hG
    obtain ⟨i, hi⟩ := hφ j (emb (T G)) (emb_pos _) hG
    obtain ⟨r, hr⟩ := exists_emb_le hi
    obtain ⟨s, hsr, hsG⟩ := compatible_of_emb_le (hr.trans inf_le_left)
    have hs : T (toHP0.symm s) = s := Equiv.apply_symm_apply _ _
    refine ⟨toHP0.symm s, (hT _ _).mp (by rw [hs]; exact hsG), i, ?_⟩
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
  have hbelow : ∀ α, α < (Order.succ μ).ord → emb (T (play start moveI α)) ≤ Γ := by
    intro α hα
    have hpure := hchain 0 α bot_le hα
    rw [h0] at hpure
    have hle : T (play start moveI α) ≤ T start := (hT _ _).mpr (WeakExtends.of_pure hpure)
    rw [hstart] at hle
    exact (emb_mono hle).trans hp₀
  have hmove : ∀ j, ∃ i, emb (T (moveI (e j) fun γ _ => play start moveI γ)) ≤ φ j i := by
    intro j
    have hlt : e j < (Order.succ μ).ord := (heρ j).trans hρ
    have hex : ∃ K, Good (e j) (play start moveI (e j)) K := by
      obtain ⟨K, hK, i, hi⟩ := hnext j _ (hbelow _ hlt)
      refine ⟨K, hK, fun j' hj' => ?_⟩
      obtain rfl := he hj'
      exact ⟨i, hi⟩
    have hm : (moveI (e j) fun γ _ => play start moveI γ) = Classical.choose hex := dif_pos hex
    rw [hm]
    exact (Classical.choose_spec hex).2 j rfl
  choose c hc using hmove
  refine ⟨T (play start moveI ρ), c, hbelow ρ hρ, fun j => ?_⟩
  exact (emb_mono ((hT _ _).mpr (hweak (e j) ρ (heρ j) hρ))).trans (hc j)

/-- Distributivity for any index type of cardinality at most `μ`. -/
theorem exists_forall_of_card_le0 {J : Type w}
    (hJ : Cardinal.lift.{u} #J ≤ Cardinal.lift.{w} μ)
    {Γ : Alg0 V I block μ hμ} (hΓ : ⊥ < Γ) {ι : J → Type*}
    (φ : ∀ j, ι j → Alg0 V I block μ hμ)
    (hφ : ∀ j (Γ' : Alg0 V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ j i) :
    ∃ (q : HP0 V I block μ hμ) (c : ∀ j, ι j), emb q ≤ Γ ∧ ∀ j, emb q ≤ φ j (c j) := by
  have hJ' : Cardinal.lift.{u} #J ≤ Cardinal.lift.{w} #(μ.ord.ToType) := by
    rwa [Cardinal.mk_toType, Cardinal.card_ord]
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hJ'
  let e : J → Ordinal.{u} := fun j => (Ordinal.ToType.mk.symm (f j)).1
  have he : Function.Injective e := by
    intro j k hjk
    exact f.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext hjk))
  exact exists_forall_of_schedule0 e he (Cardinal.ord_lt_ord.mpr (Order.lt_succ μ))
    (fun j => (Ordinal.ToType.mk.symm (f j)).2) hΓ φ hφ

/-- Distributivity for sequences indexed by the ordinals below `ρ < μ⁺`. -/
theorem exists_forall_ordinal0 {ρ : Ordinal.{u}} (hρ : ρ < (Order.succ μ).ord)
    {Γ : Alg0 V I block μ hμ} (hΓ : ⊥ < Γ) {ι : Ordinal.{u} → Type*}
    (φ : ∀ α, ι α → Alg0 V I block μ hμ)
    (hφ : ∀ α, α < ρ → ∀ (Γ' : Alg0 V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ →
      ∃ i, ⊥ < Γ' ⊓ φ α i) :
    ∃ (q : HP0 V I block μ hμ) (c : ∀ α : Set.Iio ρ, ι α.1), emb q ≤ Γ ∧
      ∀ α : Set.Iio ρ, emb q ≤ φ α.1 (c α) :=
  exists_forall_of_schedule0 (J := Set.Iio ρ) Subtype.val Subtype.val_injective hρ
    (fun α => α.2) hΓ (fun α => φ α.1) (fun α => hφ α.1 α.2)

/-! ## No new small functions over `Alg0` -/

theorem reflect_function_Alg0 {x y : PSet.{u}}
    (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j) (hxμ : #x.Type ≤ μ)
    {g : bSet (Alg0 V I block μ hμ)} {Γ : Alg0 V I block μ hμ} (hpos : ⊥ < Γ)
    (hfunc : Γ ≤ is_function (check x) (check y) g) :
    ∃ (f : PSet.{u}) (Δ : Alg0 V I block μ hμ), ⊥ < Δ ∧ Δ ≤ Γ ∧
      Δ ≤ check f =ᴮ g ∧ PSet.is_func x y f := by
  have hsup : ∀ i : x.Type, Γ ≤ ⨆ j : (check y : bSet (Alg0 V I block μ hμ)).type,
      pair (check (x.Func i)) (check (y.Func (check_cast j))) ∈ᴮ g := by
    intro i
    have htotal : Γ ≤ is_total (check x) (check y) g :=
      is_total_of_is_func' (is_func'_of_is_function hfunc)
    have hmem : Γ ≤ (check (x.Func i) : bSet (Alg0 V I block μ hμ)) ∈ᴮ check x := by
      rw [check_mem'']
      exact le_top
    have hvalue : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check (x.Func i)) w ∈ᴮ g :=
      (le_inf (htotal.trans (iInf_le _ (check (x.Func i)))) hmem).trans bv_imp_elim
    rw [← @bounded_exists (Alg0 V I block μ hμ) _ (check y)
      (fun w => pair (check (x.Func i)) w ∈ᴮ g)
      (h_congr := B_ext_pair_mem_right)] at hvalue
    simpa only [check_bval_top, top_inf_eq, check_func] using hvalue
  obtain ⟨q, c, hqΓ, hqc⟩ := exists_forall_of_card_le0 (Cardinal.lift_le.mpr hxμ) hpos
    (ι := fun _ => (check y : bSet (Alg0 V I block μ hμ)).type)
    (fun i j => pair (check (x.Func i)) (check (y.Func (check_cast j))) ∈ᴮ g)
    (fun i Γ' hΓ' hle => nonzero_inf_of_nonzero_le_supr hΓ' (hle.trans (hsup i)))
  obtain ⟨f, hf, hfis⟩ := check_eq_of_forall_pair_general hx (fun i => check_cast (c i))
    (hqΓ.trans hfunc) hqc
  exact ⟨f, emb q, emb_pos q, hqΓ, hf, hfis⟩

theorem check_functions_eq_Alg0 {x y : PSet.{u}}
    (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j) (hxμ : #x.Type ≤ μ)
    (Γ : Alg0 V I block μ hμ) :
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
  obtain ⟨f, Δ', hpos', hle, heq, hf⟩ := reflect_function_Alg0 hx hxμ hpos hfunc
  refine ⟨Δ', hpos', hle, ?_⟩
  exact bv_rw' (bv_symm heq)
    (ϕ := fun z => z ∈ᴮ check (PSet.functions x y))
    (h_congr := B_ext_mem_left)
    (H_new := check_mem ((PSet.mem_functions_iff f).mpr hf))

end Distributive

end HistoryForcing

end Erdos1220Full

#print axioms Erdos1220Full.HistoryForcing.code_injective
#print axioms Erdos1220Full.HistoryForcing.small_history
#print axioms Erdos1220Full.HistoryForcing.small_HP
#print axioms Erdos1220Full.HistoryForcing.toHP0_le_iff
#print axioms Erdos1220Full.HistoryForcing.nonempty0
#print axioms Erdos1220Full.HistoryForcing.chainCondition_Alg0
#print axioms Erdos1220Full.HistoryForcing.chainCondition_Alg0_of_antichainBound
#print axioms Erdos1220Full.HistoryForcing.exists_forall_of_schedule0
#print axioms Erdos1220Full.HistoryForcing.exists_forall_of_card_le0
#print axioms Erdos1220Full.HistoryForcing.exists_forall_ordinal0
#print axioms Erdos1220Full.HistoryForcing.reflect_function_Alg0
#print axioms Erdos1220Full.HistoryForcing.check_functions_eq_Alg0
