/-
# Erdős #1220 — the hypotheses `Sem.hyp` for a check-name `λ̌` in `V 𝔹`

Boolean-valued mirror of `Card1220`/`Cof1220`.  Everything is for an arbitrary nontrivial complete
Boolean algebra `β : Type`; the forcing-specific inputs are *explicit hypotheses*:

* (Hcc)  `Erdos1220Full.ChainCondition θ β` (antichains have size `< θ`);
* (Hdist) is used only in later sections (`ω`-sequences), see the section headers.

Each theorem states which of them it uses.
-/
import Erdos1220Full.Semantics1220
import Erdos1220Full.ChainPreservation
import Erdos1220Full.Card1220
import Erdos1220Full.Cof1220
import Erdos1220Full.CardPreserveSem
import Erdos1220.BethWitness

open Fol bSet Cardinal Lattice
open scoped Flypitch

namespace Flypitch.Erdos1220.Hyp

open Flypitch.Erdos501

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

/-! ### Small Boolean-algebra helpers -/

theorem imp_elim' {Γ a b : β} (h₁ : Γ ≤ (a ⟹ b)) (h₂ : Γ ≤ a) : Γ ≤ b :=
  (le_inf h₁ h₂).trans bv_imp_elim

theorem pair_eq_pair_eq (a b c d : bSet β) : pair a b =ᴮ pair c d = a =ᴮ c ⊓ b =ᴮ d :=
  le_antisymm
    (let h := eq_of_eq_pair (le_refl (pair a b =ᴮ pair c d)); le_inf h.1 h.2)
    (pair_congr inf_le_left inf_le_right)

/-! ### `Sem.ord`, `Sem.subset` versus Flypitch's `Ord`, `⊆ᴮ` -/

theorem subset_eq (s t : bSet β) : Flypitch.Erdos1220.Sem.subset s t = s ⊆ᴮ t :=
  subset_unfold'.symm

theorem ord_eq_Ord (a : bSet β) : Flypitch.Erdos1220.Sem.ord a = bSet.Ord a := by
  unfold Flypitch.Erdos1220.Sem.ord bSet.Ord epsilon_well_orders epsilon_trichotomy
    epsilon_well_founded is_transitive
  simp only [subset_eq]
  try rfl

/-! ### Quantifiers bounded by a check-name -/

theorem mem_check (a : bSet β) (x : PSet.{0}) :
    a ∈ᴮ check x = ⨆ i : x.Type, a =ᴮ check (x.Func i) := by
  cases x
  rw [mem_unfold]
  simp only [check_bval_top, top_inf_eq]
  rfl

theorem le_forall_check {x : PSet.{0}} {ϕ : bSet β → β} (hϕ : B_ext ϕ) {Γ : β}
    (h : ∀ i : x.Type, Γ ≤ ϕ (check (x.Func i))) :
    Γ ≤ ⨅ a : bSet β, a ∈ᴮ check x ⟹ ϕ a := by
  refine le_iInf fun a => bv_imp_intro_lemma ?_
  rw [mem_check, inf_iSup_eq]
  refine iSup_le fun i => ?_
  have h1 : Γ ⊓ a =ᴮ check (x.Func i) ≤ check (x.Func i) =ᴮ a ⊓ ϕ (check (x.Func i)) :=
    le_inf (inf_le_right.trans (le_of_eq bv_eq_symm)) (inf_le_left.trans (h i))
  exact h1.trans (hϕ _ _)

theorem check_le_exists {x : PSet.{0}} {ϕ : bSet β → β} {Γ : β} (i : x.Type)
    (h : Γ ≤ ϕ (check (x.Func i))) : Γ ≤ ⨆ a : bSet β, a ∈ᴮ check x ⊓ ϕ a :=
  le_iSup_of_le (check (x.Func i)) (le_inf (le_top.trans (check_mem'').ge) h)

theorem exists_check_le {x : PSet.{0}} {ϕ : bSet β → β} (hϕ : B_ext ϕ) :
    (⨆ a : bSet β, a ∈ᴮ check x ⊓ ϕ a) ≤ ⨆ i : x.Type, ϕ (check (x.Func i)) := by
  refine iSup_le fun a => ?_
  rw [mem_check, iSup_inf_eq]
  exact iSup_le fun i => le_iSup_of_le i (hϕ _ _)

/-! ### Graph names of ground functions -/

/-- The name `{(x̌ᵢ, y̌_{e i}) | i}` of the graph of `e`. -/
def graph (x y : PSet.{0}) (e : x.Type → y.Type) : bSet β :=
  bSet.mk x.Type (fun i => pair (check (x.Func i)) (check (y.Func (e i)))) (fun _ => ⊤)

theorem app_graph (x y : PSet.{0}) (e : x.Type → y.Type) (a b : bSet β) :
    Sem.app (graph x y e) a b =
      ⨆ i : x.Type, a =ᴮ check (x.Func i) ⊓ b =ᴮ check (y.Func (e i)) := by
  have h : Sem.app (graph x y e) a b =
      ⨆ i : x.Type, ⊤ ⊓ pair a b =ᴮ pair (check (x.Func i)) (check (y.Func (e i))) :=
    mem_unfold
  rw [h]
  simp only [top_inf_eq, pair_eq_pair_eq]

theorem B_ext_isFun_body (g D : bSet β) :
    B_ext (fun a => ⨆ y : bSet β, y ∈ᴮ D ⊓
      (Sem.app g a y ⊓ ⨅ y' : bSet β, Sem.app g a y' ⟹ y' =ᴮ y)) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const (B_ext_inf B_ext_pair_mem_left
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_pair_mem_left) (h₂ := B_ext_const)))))

/-- The graph of `e` is a function `x̌ → y̌` if `e` respects equivalence. -/
theorem isFun_graph (x y : PSet.{0}) (e : x.Type → y.Type)
    (hR1 : ∀ i k, PSet.Equiv (x.Func i) (x.Func k) → PSet.Equiv (y.Func (e i)) (y.Func (e k))) :
    (⊤ : β) ≤ Sem.isFun (check x) (check y) (graph x y e) := by
  unfold Sem.isFun
  refine le_forall_check (B_ext_isFun_body _ _) fun i => ?_
  refine check_le_exists (e i) (le_inf ?_ ?_)
  · rw [app_graph]
    exact le_iSup_of_le i (le_inf bv_refl bv_refl)
  · refine le_iInf fun b' => bv_imp_intro_lemma ?_
    rw [app_graph, inf_iSup_eq]
    refine iSup_le fun k => ?_
    by_cases hik : PSet.Equiv (x.Func i) (x.Func k)
    · have h1 : (⊤ : β) ≤ check (y.Func (e k)) =ᴮ check (y.Func (e i)) :=
        check_eq (hR1 i k hik).symm
      exact bv_trans (inf_le_right.trans inf_le_right) (le_top.trans h1)
    · have h0 : (check (x.Func i) =ᴮ check (x.Func k) : β) = ⊥ :=
        check_bv_eq_bot_of_not_equiv hik
      refine le_trans ?_ bot_le
      rw [← h0]
      exact inf_le_right.trans inf_le_left

/-- Injectivity of the graph of `e` if `e` reflects equivalence. -/
theorem app_graph_inj (x y : PSet.{0}) (e : x.Type → y.Type)
    (hR2 : ∀ i k, PSet.Equiv (y.Func (e i)) (y.Func (e k)) → PSet.Equiv (x.Func i) (x.Func k))
    (a a' b : bSet β) :
    Sem.app (graph x y e) a b ⊓ Sem.app (graph x y e) a' b ≤ a =ᴮ a' := by
  rw [app_graph, app_graph, iSup_inf_eq]
  refine iSup_le fun i => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun k => ?_
  by_cases h : PSet.Equiv (y.Func (e i)) (y.Func (e k))
  · have hx : (⊤ : β) ≤ check (x.Func i) =ᴮ check (x.Func k) := check_eq (hR2 i k h)
    exact bv_trans (bv_trans (inf_le_left.trans inf_le_left) (le_top.trans hx))
      (bv_symm (inf_le_right.trans inf_le_left))
  · have hy : (check (y.Func (e i)) =ᴮ check (y.Func (e k)) : β) = ⊥ :=
      check_bv_eq_bot_of_not_equiv h
    refine le_trans ?_ bot_le
    rw [← hy]
    exact bv_trans (bv_symm (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right)

/-- The injectivity clause of `Sem.leq` from a pointwise bound. -/
theorem le_inj_clause {A f : bSet β} {Γ : β}
    (h : ∀ a a' b : bSet β, Sem.app f a b ⊓ Sem.app f a' b ≤ a =ᴮ a') :
    Γ ≤ ⨅ x : bSet β, x ∈ᴮ A ⟹ ⨅ x' : bSet β, x' ∈ᴮ A ⟹ ⨅ y : bSet β,
      Sem.app f x y ⟹ (Sem.app f x' y ⟹ x =ᴮ x') := by
  refine le_iInf fun a => bv_imp_intro_lemma (le_iInf fun a' => bv_imp_intro_lemma
    (le_iInf fun b => bv_imp_intro_lemma (bv_imp_intro_lemma ?_)))
  exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans (h a a' b)

/-- **Ground injections give injections in `V 𝔹`** (no hypothesis on `β`). -/
theorem leq_check_of (x y : PSet.{0}) (e : x.Type → y.Type)
    (hR1 : ∀ i k, PSet.Equiv (x.Func i) (x.Func k) → PSet.Equiv (y.Func (e i)) (y.Func (e k)))
    (hR2 : ∀ i k, PSet.Equiv (y.Func (e i)) (y.Func (e k)) → PSet.Equiv (x.Func i) (x.Func k)) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.leq (check x) (check y) := by
  unfold Flypitch.Erdos1220.Sem.leq
  exact le_iSup_of_le (graph x y e)
    (le_inf (isFun_graph x y e hR1) (le_inj_clause (app_graph_inj x y e hR2)))

theorem leq_check_of_injective (x y : PSet.{0})
    (hx : ∀ i j, i ≠ j → ¬ PSet.Equiv (x.Func i) (x.Func j))
    (hy : ∀ i j, i ≠ j → ¬ PSet.Equiv (y.Func i) (y.Func j))
    (e : x.Type → y.Type) (he : Function.Injective e) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.leq (check x) (check y) := by
  refine leq_check_of x y e (fun i k h => ?_) (fun i k h => ?_)
  · by_cases hik : i = k
    · subst hik; exact PSet.Equiv.refl _
    · exact absurd h (hx i k hik)
  · by_cases hik : e i = e k
    · have hik' := he hik
      subst hik'
      exact PSet.Equiv.refl _
    · exact absurd h (hy _ _ hik)

/-! ### Monotonicity and extensionality of `Sem.leq` in the codomain -/

theorem isFun_mono_cod {A B B' f : bSet β} {Γ : β} (hsub : Γ ≤ B ⊆ᴮ B')
    (h : Γ ≤ Sem.isFun A B f) : Γ ≤ Sem.isFun A B' f := by
  unfold Sem.isFun at h ⊢
  refine le_iInf fun a => bv_imp_intro_lemma ?_
  have h1 := imp_elim' ((inf_le_left : Γ ⊓ a ∈ᴮ A ≤ Γ).trans (h.trans (iInf_le _ a))) inf_le_right
  refine (le_inf inf_le_left h1).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun y => le_iSup_of_le y (le_inf ?_ (inf_le_right.trans inf_le_right))
  exact mem_of_mem_subset (inf_le_left.trans hsub) (inf_le_right.trans inf_le_left)

theorem leq_mono_right {A B B' : bSet β} {Γ : β} (hsub : Γ ≤ B ⊆ᴮ B')
    (h : Γ ≤ Flypitch.Erdos1220.Sem.leq A B) : Γ ≤ Flypitch.Erdos1220.Sem.leq A B' := by
  unfold Flypitch.Erdos1220.Sem.leq at h ⊢
  refine (le_inf le_rfl h).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun f => le_iSup_of_le f (le_inf ?_ (inf_le_right.trans inf_le_right))
  exact isFun_mono_cod (inf_le_left.trans hsub) (inf_le_right.trans inf_le_left)

theorem B_ext_isFun_cod (A f : bSet β) : B_ext (fun B => Sem.isFun A B f) := by
  unfold Sem.isFun
  exact B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_mem_right B_ext_const)))

theorem B_ext_leq_right (A : bSet β) : B_ext (fun B => Flypitch.Erdos1220.Sem.leq A B) := by
  unfold Flypitch.Erdos1220.Sem.leq
  exact B_ext_iSup (h := fun f => B_ext_inf (B_ext_isFun_cod A f) B_ext_const)

/-! ### (Hcc) No injection of a large check-name into a small one -/

section noInj

variable {θ : Cardinal.{0}}

/-- Core of the chain-condition argument, for a single candidate `f`. Uses (Hcc). -/
theorem leq_body_le_bot (hcc : Erdos1220Full.ChainCondition θ β)
    (x y : PSet.{0}) (hx : ∀ i j, i ≠ j → ¬ PSet.Equiv (x.Func i) (x.Func j))
    {T : Type} (c : y.Type → T) (hc : ∀ j j', c j = c j' → PSet.Equiv (y.Func j) (y.Func j'))
    (hθ : θ ≤ #T) (hTx : #T < #x.Type) (hω : ℵ₀ ≤ #x.Type) (f : bSet β) :
    Sem.isFun (check x) (check y) f ⊓ (⨅ a : bSet β, a ∈ᴮ check x ⟹ ⨅ a' : bSet β,
      a' ∈ᴮ check x ⟹ ⨅ b : bSet β, Sem.app f a b ⟹ (Sem.app f a' b ⟹ a =ᴮ a')) ≤ ⊥ := by
  classical
  by_contra hne
  set Γ := Sem.isFun (check x) (check y) f ⊓ (⨅ a : bSet β, a ∈ᴮ check x ⟹ ⨅ a' : bSet β,
      a' ∈ᴮ check x ⟹ ⨅ b : bSet β, Sem.app f a b ⟹ (Sem.app f a' b ⟹ a =ᴮ a')) with hΓ
  have hpos : ⊥ < Γ := bot_lt_iff_ne_bot.2 fun h => hne h.le
  -- values of `f` on `x̌ᵢ` lie in `y̌`
  have hval : ∀ i : x.Type, Γ ≤ ⨆ j : y.Type, Sem.app f (check (x.Func i)) (check (y.Func j)) := by
    intro i
    have h1 := imp_elim' ((inf_le_left : Γ ≤ _).trans (iInf_le _ (check (x.Func i))))
      (le_top.trans (check_mem'').ge)
    refine h1.trans ?_
    refine le_trans (iSup_mono fun b => inf_le_inf_left _ inf_le_left) ?_
    exact exists_check_le B_ext_pair_mem_right
  -- injectivity on `x̌`
  have hinj : ∀ (i k : x.Type) (b : bSet β),
      Γ ⊓ Sem.app f (check (x.Func i)) b ⊓ Sem.app f (check (x.Func k)) b ≤
        check (x.Func i) =ᴮ check (x.Func k) := by
    intro i k b
    have h0 : Γ ⊓ Sem.app f (check (x.Func i)) b ⊓ Sem.app f (check (x.Func k)) b ≤ Γ :=
      inf_le_left.trans inf_le_left
    have h1 := imp_elim' ((h0.trans inf_le_right).trans (iInf_le _ (check (x.Func i))))
      (le_top.trans (check_mem'').ge)
    have h2 := imp_elim' (h1.trans (iInf_le _ (check (x.Func k)))) (le_top.trans (check_mem'').ge)
    have h3 := imp_elim' (h2.trans (iInf_le _ b)) (inf_le_left.trans inf_le_right)
    exact imp_elim' h3 inf_le_right
  choose g hg using fun i => nonzero_inf_of_nonzero_le_supr hpos (hval i)
  obtain ⟨t, ht⟩ := Cardinal.infinite_pigeonhole_card_lt (c ∘ g) hTx hω
  let a : ((c ∘ g) ⁻¹' {t}) → β := fun i =>
    Γ ⊓ Sem.app f (check (x.Func i.1)) (check (y.Func (g i.1)))
  have hsmall := hcc _ a (fun i => hg i.1) (by
    intro i i' hii'
    have hne' : i.1 ≠ i'.1 := fun h => hii' (Subtype.ext h)
    have hci : c (g i.1) = c (g i'.1) := by
      have h1 : (c ∘ g) i.1 = t := i.2
      have h2 : (c ∘ g) i'.1 = t := i'.2
      exact h1.trans h2.symm
    have hyeq : (⊤ : β) ≤ check (y.Func (g i'.1)) =ᴮ check (y.Func (g i.1)) :=
      check_eq (hc _ _ hci).symm
    have hmove : Sem.app f (check (x.Func i'.1)) (check (y.Func (g i'.1))) ≤
        Sem.app f (check (x.Func i'.1)) (check (y.Func (g i.1))) :=
      (le_inf (le_top.trans hyeq) le_rfl).trans (B_ext_pair_mem_right _ _)
    have hbot : (check (x.Func i.1) =ᴮ check (x.Func i'.1) : β) = ⊥ :=
      check_bv_eq_bot_of_not_equiv (hx _ _ hne')
    rw [← hbot]
    refine le_trans ?_ (hinj i.1 i'.1 (check (y.Func (g i.1))))
    exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
      ((inf_le_right.trans inf_le_right).trans hmove))
  exact absurd (hθ.trans ht.le) (not_le.2 hsmall)

/-- **No injection `x̌ → y̌`** when the classes of `y` are fewer than the elements of `x`
and at least `θ` (uses (Hcc)). -/
theorem leq_check_eq_bot (hcc : Erdos1220Full.ChainCondition θ β)
    (x y : PSet.{0}) (hx : ∀ i j, i ≠ j → ¬ PSet.Equiv (x.Func i) (x.Func j))
    {T : Type} (c : y.Type → T) (hc : ∀ j j', c j = c j' → PSet.Equiv (y.Func j) (y.Func j'))
    (hθ : θ ≤ #T) (hTx : #T < #x.Type) (hω : ℵ₀ ≤ #x.Type) :
    Flypitch.Erdos1220.Sem.leq (check x) (check y) = (⊥ : β) := by
  unfold Flypitch.Erdos1220.Sem.leq
  exact le_bot_iff.mp (iSup_le fun f => leq_body_le_bot hcc x y hx c hc hθ hTx hω f)

end noInj

/-! ### Ground injections from cardinalities (`ZFSet` level, no hypothesis on `β`) -/

theorem injects_into_of_card_le {x y : PSet.{0}}
    (h : ZFSet.card (ZFSet.mk x) ≤ ZFSet.card (ZFSet.mk y)) : PSet.injects_into x y := by
  obtain ⟨e, he⟩ := _root_.Erdos1220.FOL.exists_graph_of_card_le h
  refine ⟨(_root_.Erdos1220.FOL.graphZ e).out,
    show PSet.is_func x y _ ∧ PSet.is_inj _ from ⟨?_, ?_⟩⟩
  · show ZFSet.IsFunc (ZFSet.mk x) (ZFSet.mk y) (ZFSet.mk (_root_.Erdos1220.FOL.graphZ e).out)
    rw [ZFSet.mk_out, ← ZFSet.mem_funs]
    exact _root_.Erdos1220.FOL.graphZ_mem_funs _ _ e
  · intro w₁ w₂ v₁ v₂ ⟨h1, h2, h3⟩
    rw [← ZFSet.mk_mem_iff, PSet.pSet_pair_sound, ZFSet.mk_out] at h1 h2
    obtain ⟨hx1, e1⟩ := (_root_.Erdos1220.FOL.pair_mem_graphZ e).1 h1
    obtain ⟨hx2, e2⟩ := (_root_.Erdos1220.FOL.pair_mem_graphZ e).1 h2
    have hv : ZFSet.mk v₁ = ZFSet.mk v₂ := ZFSet.sound h3
    have := he (Subtype.ext (e1.trans (hv.trans e2.symm)))
    exact ZFSet.exact (congrArg Subtype.val this)

theorem mk_functions (x y : PSet.{0}) :
    ZFSet.mk (PSet.functions x y) = ZFSet.funs (ZFSet.mk x) (ZFSet.mk y) := by
  ext z
  refine Quotient.inductionOn z fun p => ?_
  change ZFSet.mk p ∈ _ ↔ ZFSet.mk p ∈ _
  rw [ZFSet.mk_mem_iff, PSet.mem_functions_iff, ZFSet.mem_funs]

theorem card_mk_ordinalMk (o : Ordinal.{0}) :
    ZFSet.card (ZFSet.mk (PSet.ordinalMk o)) = o.card := by
  rw [Ordinal.mk_toPSet, Ordinal.card_toZFSet]

theorem card_mk_omega : ZFSet.card (ZFSet.mk PSet.omega.{0}) = ℵ₀ :=
  _root_.Erdos1220.FOL.card_omega

theorem card_mk_functions_omega (μ : PSet.{0}) :
    ZFSet.card (ZFSet.mk (PSet.functions PSet.omega μ)) = ZFSet.card (ZFSet.mk μ) ^ ℵ₀ := by
  rw [mk_functions, _root_.Erdos1220.FOL.card_funs, card_mk_omega]

/-! ### Extensionality of `Sem.fn`, `Sem.powLt`, `Sem.omegaInacc` -/

theorem B_ext_fn_cod (D f : bSet β) : B_ext (fun C => Flypitch.Erdos1220.Sem.fn D C f) := by
  unfold Flypitch.Erdos1220.Sem.fn
  exact B_ext_inf (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_iSup
    (h := fun _ => B_ext_inf B_ext_const (B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_mem_right B_ext_const)))))) B_ext_const

theorem B_ext_powLt_left (k : bSet β) : B_ext (fun μ => Flypitch.Erdos1220.Sem.powLt μ k) := by
  unfold Flypitch.Erdos1220.Sem.powLt
  exact B_ext_iSup (h := fun _ => B_ext_inf B_ext_const (B_ext_iSup (h := fun _ => B_ext_inf
    (B_ext_iInf (h := fun f => B_ext_imp (h₁ := B_ext_fn_cod _ f) (h₂ := B_ext_const)))
    (B_ext_iInf (h := fun f => B_ext_iInf (h := fun f' => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_fn_cod _ f) (h₂ := B_ext_imp (h₁ := B_ext_fn_cod _ f')
        (h₂ := B_ext_const)))))))))

theorem B_ext_powLt_right (μ : bSet β) : B_ext (fun k => Flypitch.Erdos1220.Sem.powLt μ k) := by
  unfold Flypitch.Erdos1220.Sem.powLt
  exact B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)

theorem B_ext_omegaInacc : B_ext (fun d : bSet β => Flypitch.Erdos1220.Sem.omegaInacc d) := by
  unfold Flypitch.Erdos1220.Sem.omegaInacc
  exact B_ext_iInf (h := fun μ => B_ext_imp (h₁ := B_ext_mem_right)
    (h₂ := B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_powLt_right μ)))

/-! ### (Hdist) `ℵ₀`-inaccessibility of `κ̌`

`HF` is the countable-closure hypothesis: the `ω`-sequences into an ordinal `ǒ` in `V 𝔹` are the
check of the ground set of `ω`-sequences (for the concrete algebra: `check_functions_eq_CAlg`). -/

/-- (Hdist) as used here. -/
def HF (β : Type) [NontrivialCompleteBooleanAlgebra β] : Prop :=
  ∀ o : Ordinal.{0}, (⊤ : β) ≤
    check (PSet.functions PSet.omega (PSet.ordinalMk o)) =ᴮ
      functions bSet.omega (check (PSet.ordinalMk o))

/-- Uses (Hdist) only. -/
theorem powLt_check_ordinal (hF : HF β) {κ : Cardinal.{0}}
    (hκ : _root_.Erdos1220.IsOmegaInaccessible κ) {o : Ordinal.{0}} (ho : o < κ.ord) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.powLt (check (PSet.ordinalMk o))
      (check (PSet.card_ex κ)) := by
  have hlt : o.card ^ ℵ₀ < κ := hκ _ (Cardinal.lt_ord.1 ho)
  refine Erdos1220Full.CardB.powLtB_check (α := PSet.ordinalMk (o.card ^ ℵ₀).ord)
    (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.2 hlt)) ?_ (hF o)
  apply injects_into_of_card_le
  rw [card_mk_functions_omega, card_mk_ordinalMk, card_mk_ordinalMk, Cardinal.card_ord]

/-- **`ℵ₀`-inaccessibility of a ground `ℵ₀`-inaccessible cardinal persists.** Uses (Hdist) only. -/
theorem omegaInacc_card_ex (hF : HF β) {κ : Cardinal.{0}}
    (hκ : _root_.Erdos1220.IsOmegaInaccessible κ) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.omegaInacc (check (PSet.card_ex κ)) := by
  have h1 : (⊤ : β) ≤ ⨅ μ : bSet β, μ ∈ᴮ check (PSet.card_ex κ) ⟹
      Flypitch.Erdos1220.Sem.powLt μ (check (PSet.card_ex κ)) := by
    refine le_forall_check (B_ext_powLt_left _) fun i => ?_
    obtain ⟨o, ho, heq⟩ := Erdos1220Full.CardB.card_ex_func_equiv κ i
    exact bv_rw' (check_eq heq) (ϕ := fun μ => Flypitch.Erdos1220.Sem.powLt μ
      (check (PSet.card_ex κ))) (h_congr := B_ext_powLt_left _)
      (H_new := powLt_check_ordinal hF hκ ho)
  unfold Flypitch.Erdos1220.Sem.omegaInacc
  refine le_iInf fun μ => bv_imp_intro_lemma (bv_imp_intro_lemma ?_)
  exact imp_elim' ((inf_le_left.trans inf_le_left).trans (h1.trans (iInf_le _ μ)))
    (inf_le_left.trans inf_le_right)

/-! ### (Hcc) singularity of `λ̌` -/

/-- **A ground singular cardinal stays singular** (witnessed by a ground cofinal set of size
`cf λ`). Uses (Hcc) only, with `θ ≤ cf λ`. -/
theorem singular_card_ex {θ : Cardinal.{0}} (hcc : Erdos1220Full.ChainCondition θ β)
    {lam : Cardinal.{0}} (hsing : lam.IsSingular) (hθ : θ ≤ lam.ord.cof) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.singular (check (PSet.card_ex lam)) := by
  classical
  have hlamcard : ZFSet.card (ZFSet.mk (PSet.card_ex lam)) = lam := by
    show ZFSet.card (ZFSet.mk (PSet.ordinalMk lam.ord)) = lam
    rw [card_mk_ordinalMk, Cardinal.card_ord]
  have hlamType : #(PSet.card_ex lam).Type = lam := by
    show #(PSet.ordinalMk lam.ord).Type = lam
    rw [PSet.ordinalMk_type, Cardinal.mk_toType, Cardinal.card_ord]
  unfold Flypitch.Erdos1220.Sem.singular
  refine le_inf ?_ ?_
  · have hω : PSet.injects_into PSet.omega (PSet.card_ex lam) :=
      injects_into_of_card_le (by rw [hlamcard, card_mk_omega]; exact hsing.aleph0_le)
    exact Erdos1220Full.CardB.sem_leq_check_of_injects hω
  · obtain ⟨S, hS, hc, hcard⟩ := _root_.Erdos1220.FOL.exists_cofinal_card_eq lam.ord
    set Sg : PSet.{0} := S.out with hSg
    have hmkS : ZFSet.mk Sg = S := ZFSet.mk_out S
    have hsub : Sg ⊆ PSet.card_ex lam := by
      refine PSet.subset_iff.2 fun z hz => ?_
      rw [← ZFSet.mk_mem_iff, hmkS] at hz
      rw [← ZFSet.mk_mem_iff]
      show ZFSet.mk z ∈ ZFSet.mk (lam.ord.toPSet)
      rw [Ordinal.mk_toPSet]
      exact hS _ hz
    have hcofg : ∀ i : (PSet.card_ex lam).Type, ∃ j : Sg.Type,
        (PSet.card_ex lam).Func i ∈ Sg.Func j ∨
          PSet.Equiv ((PSet.card_ex lam).Func i) (Sg.Func j) := by
      intro i
      have hm : ZFSet.mk ((PSet.card_ex lam).Func i) ∈ lam.ord.toZFSet := by
        rw [← Ordinal.mk_toPSet, ZFSet.mk_mem_iff]
        exact PSet.func_mem _ i
      obtain ⟨g, hgS, hg⟩ := hc _ hm
      have hgS' : g.out ∈ Sg := by
        rw [← ZFSet.mk_mem_iff, hmkS, ZFSet.mk_out]; exact hgS
      obtain ⟨j, hj⟩ := PSet.mem_def.1 hgS'
      have hgj : ZFSet.mk (Sg.Func j) = g := by rw [← ZFSet.sound hj, ZFSet.mk_out]
      refine ⟨j, ?_⟩
      rcases hg with h | h
      · left; rw [← ZFSet.mk_mem_iff, hgj]; exact h
      · right; exact ZFSet.exact (h.trans hgj.symm)
    have hmemS : ∀ j : Sg.Type, ZFSet.mk (Sg.Func j) ∈ S := by
      intro j
      have := PSet.func_mem Sg j
      rw [← ZFSet.mk_mem_iff, hmkS] at this
      exact this
    let c : Sg.Type → Shrink.{0} S := fun j => equivShrink S ⟨ZFSet.mk (Sg.Func j), hmemS j⟩
    have hcc' : ∀ j j', c j = c j' → PSet.Equiv (Sg.Func j) (Sg.Func j') := by
      intro j j' h
      have := congrArg Subtype.val ((equivShrink S).injective h)
      exact ZFSet.exact this
    have hT : #(Shrink.{0} S) = lam.ord.cof := hcard
    have hbot := leq_check_eq_bot hcc (PSet.card_ex lam) Sg
      (Erdos1220Full.CardB.card_ex_inj lam) c hcc' (hT ▸ hθ)
      (by rw [hT, hlamType]; exact hsing.cof_ord_lt) (by rw [hlamType]; exact hsing.aleph0_le)
      (β := β)
    refine le_iSup_of_le (check Sg) (le_inf ?_ (le_inf ?_ ?_))
    · exact Erdos1220Full.CardB.subsetB_check hsub
    · exact Erdos1220Full.CardB.sem_cofinal_check hcofg
    · rw [hbot, compl_bot]

/-! ### Assembly: `⊤ ≤ Sem.hyp λ̌` -/

/-- (Hcof) the cofinality of `λ̌` in `V 𝔹` is `(cf λ)ˇ`: every `d` that `Sem.cof` declares to be
the cofinality of `λ̌` equals `(card_ex (cf λ))ˇ`.  This is the one input *not* derived here. -/
def HCof (β : Type) [NontrivialCompleteBooleanAlgebra β] (lam : Cardinal.{0}) : Prop :=
  (⊤ : β) ≤ ⨅ d : bSet β, Flypitch.Erdos1220.Sem.cof (check (PSet.card_ex lam)) d ⟹
    d =ᴮ check (PSet.card_ex lam.ord.cof)

/-- The fourth conjunct of `Sem.hyp` from (Hcof) and (Hdist). -/
theorem cof_omegaInacc_of (hF : HF β) {lam : Cardinal.{0}}
    (hκ : _root_.Erdos1220.IsOmegaInaccessible lam.ord.cof) (hcof : HCof β lam) :
    (⊤ : β) ≤ ⨅ d : bSet β, Flypitch.Erdos1220.Sem.cof (check (PSet.card_ex lam)) d ⟹
      Flypitch.Erdos1220.Sem.omegaInacc d := by
  refine le_iInf fun d => bv_imp_intro_lemma ?_
  have hd := imp_elim' ((inf_le_left : (⊤ : β) ⊓ _ ≤ ⊤).trans (hcof.trans (iInf_le _ d)))
    inf_le_right
  exact bv_rw' hd (ϕ := fun d => Flypitch.Erdos1220.Sem.omegaInacc d)
    (h_congr := B_ext_omegaInacc) (H_new := le_top.trans (omegaInacc_card_ex hF hκ))

/-- **`⊤ ≤ Sem.hyp λ̌`** for a ground cardinal satisfying the hypotheses of #1220, from
(Hcc) with `θ` regular, `θ ≤ cf λ`; (Hdist) `HF`; and (Hcof). -/
theorem hyp_card_ex {θ : Cardinal.{0}} (hcc : Erdos1220Full.ChainCondition θ β)
    (hθreg : θ.IsRegular) (hF : HF β) {lam : Cardinal.{0}}
    (hH : _root_.Erdos1220.Hypotheses lam) (hθ : θ ≤ lam.ord.cof) (hcof : HCof β lam) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.hyp (check (PSet.card_ex lam)) := by
  obtain ⟨hsing, hinacc, hinacc_cof⟩ := hH
  unfold Flypitch.Erdos1220.Sem.hyp
  refine le_inf ?_ (le_inf ?_ (le_inf ?_ ?_))
  · exact Erdos1220Full.CardB.sem_cardinal_card_ex_of_chainCondition hcc hθreg
      (hθ.trans (Ordinal.cof_ord_le lam))
  · exact singular_card_ex hcc hsing hθ
  · exact omegaInacc_card_ex hF hinacc
  · exact cof_omegaInacc_of hF hinacc_cof hcof

/-- The Beth witness `λ = ℶ_{𝔠⁺}` (`Erdos1220.bethWitness`): `cf λ = 𝔠⁺`. -/
theorem hyp_bethWitness {θ : Cardinal.{0}} (hcc : Erdos1220Full.ChainCondition θ β)
    (hθreg : θ.IsRegular) (hF : HF β)
    (hθ : θ ≤ Order.succ (Cardinal.continuum : Cardinal.{0}))
    (hcof : HCof β _root_.Erdos1220.bethWitness.{0}) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.hyp (check (PSet.card_ex _root_.Erdos1220.bethWitness.{0})) :=
  hyp_card_ex hcc hθreg hF _root_.Erdos1220.bethWitness_hypotheses
    (by rw [_root_.Erdos1220.cof_bethWitness]; exact hθ) hcof

/-! ### A ground cofinal subset of `λ` of size `cf λ` (no hypothesis on `β`) -/

/-- The `PSet` enumerating a `ZFSet` without repetitions, indexed by `Shrink`. -/
noncomputable def enumPSet (S : ZFSet.{0}) : PSet.{0} :=
  ⟨Shrink.{0} S, fun a => ((equivShrink.{0} S).symm a).1.out⟩

theorem mk_enumPSet_func (S : ZFSet.{0}) (a : (enumPSet S).Type) :
    ZFSet.mk ((enumPSet S).Func a) = ((equivShrink.{0} S).symm a).1 :=
  ZFSet.mk_out _

theorem mk_enumPSet (S : ZFSet.{0}) : ZFSet.mk (enumPSet S) = S := by
  ext z
  refine Quotient.inductionOn z fun p => ?_
  change ZFSet.mk p ∈ ZFSet.mk (enumPSet S) ↔ ZFSet.mk p ∈ S
  rw [ZFSet.mk_mem_iff, PSet.mem_def]
  constructor
  · rintro ⟨a, ha⟩
    rw [ZFSet.sound ha, mk_enumPSet_func]
    exact ((equivShrink.{0} S).symm a).2
  · intro hp
    let j : (enumPSet S).Type := equivShrink.{0} S ⟨ZFSet.mk p, hp⟩
    refine ⟨j, ZFSet.exact ?_⟩
    rw [mk_enumPSet_func]
    simp [j]

theorem enumPSet_inj (S : ZFSet.{0}) (j j' : (enumPSet S).Type) (hjj : j ≠ j') :
    ¬ PSet.Equiv ((enumPSet S).Func j) ((enumPSet S).Func j') := by
  intro h
  apply hjj
  have h1 := ZFSet.sound h
  rw [mk_enumPSet_func, mk_enumPSet_func] at h1
  exact (equivShrink.{0} S).symm.injective (Subtype.ext h1)

theorem mk_enumPSet_type (S : ZFSet.{0}) : #(enumPSet S).Type = ZFSet.card S := rfl

/-- A ground cofinal subset `Sg ⊆ λ`, indexed without repetitions by a type of size `cf λ`. -/
theorem exists_ground_cofinal (lam : Cardinal.{0}) :
    ∃ Sg : PSet.{0}, #Sg.Type = lam.ord.cof ∧
      ZFSet.card (ZFSet.mk Sg) = lam.ord.cof ∧
      Sg ⊆ PSet.card_ex lam ∧
      (∀ i : (PSet.card_ex lam).Type, ∃ j : Sg.Type,
        (PSet.card_ex lam).Func i ∈ Sg.Func j ∨
          PSet.Equiv ((PSet.card_ex lam).Func i) (Sg.Func j)) ∧
      (∀ j j', j ≠ j' → ¬ PSet.Equiv (Sg.Func j) (Sg.Func j')) := by
  classical
  obtain ⟨S, hS, hc, hcard⟩ := _root_.Erdos1220.FOL.exists_cofinal_card_eq lam.ord
  refine ⟨enumPSet S, (mk_enumPSet_type S).trans hcard, by rw [mk_enumPSet]; exact hcard,
    ?_, ?_, enumPSet_inj S⟩
  · refine PSet.subset_iff.2 fun z hz => ?_
    rw [← ZFSet.mk_mem_iff, mk_enumPSet] at hz
    rw [← ZFSet.mk_mem_iff]
    show ZFSet.mk z ∈ ZFSet.mk (lam.ord.toPSet)
    rw [Ordinal.mk_toPSet]
    exact hS _ hz
  · intro i
    have hm : ZFSet.mk ((PSet.card_ex lam).Func i) ∈ lam.ord.toZFSet := by
      rw [← Ordinal.mk_toPSet, ZFSet.mk_mem_iff]
      exact PSet.func_mem _ i
    obtain ⟨g, hgS, hg⟩ := hc _ hm
    let j : (enumPSet S).Type := equivShrink.{0} S ⟨g, hgS⟩
    have hgj : ZFSet.mk ((enumPSet S).Func j) = g := by
      rw [mk_enumPSet_func]
      simp [j]
    refine ⟨j, ?_⟩
    rcases hg with h | h
    · left; rw [← ZFSet.mk_mem_iff, hgj]; exact h
    · right; exact ZFSet.exact (h.trans hgj.symm)

/-- `ω`'s elements are pairwise non-equivalent. -/
theorem omega_func_inj : ∀ i j : PSet.omega.{0}.Type,
    PSet.Equiv (PSet.omega.Func i) (PSet.omega.Func j) → i = j := by
  intro i j h
  have h1 : _root_.Erdos1220.FOL.natZ i.down = _root_.Erdos1220.FOL.natZ j.down := ZFSet.sound h
  rw [_root_.Erdos1220.FOL.natZ_eq_toZFSet, _root_.Erdos1220.FOL.natZ_eq_toZFSet] at h1
  have h2 := Ordinal.toZFSet_injective h1
  exact ULift.down_injective (by exact_mod_cast h2)

/-! ### (Hdist) singularity of `λ̌` via distributivity -/

/-- **A ground singular cardinal stays singular**, using `DistribHyp ν` with `cf λ ≤ ν`
(no chain condition). -/
theorem singular_card_ex_of_distrib {ν : Cardinal.{0}} (hd : Erdos1220Full.CardB.DistribHyp ν β)
    {lam : Cardinal.{0}} (hsing : lam.IsSingular) (hcofν : lam.ord.cof ≤ ν) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.singular (check (PSet.card_ex lam)) := by
  have hlamcard : ZFSet.card (ZFSet.mk (PSet.card_ex lam)) = lam := by
    show ZFSet.card (ZFSet.mk (PSet.ordinalMk lam.ord)) = lam
    rw [card_mk_ordinalMk, Cardinal.card_ord]
  have hlamType : #(PSet.card_ex lam).Type = lam := by
    show #(PSet.ordinalMk lam.ord).Type = lam
    rw [PSet.ordinalMk_type, Cardinal.mk_toType, Cardinal.card_ord]
  obtain ⟨Sg, hSgT, -, hsub, hcofg, -⟩ := exists_ground_cofinal lam
  unfold Flypitch.Erdos1220.Sem.singular
  refine le_inf ?_ ?_
  · have hω : PSet.injects_into PSet.omega (PSet.card_ex lam) :=
      injects_into_of_card_le (by rw [hlamcard, card_mk_omega]; exact hsing.aleph0_le)
    exact Erdos1220Full.CardB.sem_leq_check_of_injects hω
  · have hbot := Erdos1220Full.CardB.sem_leq_check_eq_bot_of_distrib (β := β) hd Sg
      (PSet.card_ex lam) (Erdos1220Full.CardB.card_ex_inj lam) (hSgT ▸ hcofν)
      (by rw [hSgT, hlamType]; exact hsing.cof_ord_lt)
    refine le_iSup_of_le (check Sg) (le_inf ?_ (le_inf ?_ ?_))
    · exact Erdos1220Full.CardB.subsetB_check hsub
    · exact Erdos1220Full.CardB.sem_cofinal_check hcofg
    · rw [hbot, compl_bot]

/-! ### The facts about `κ̌ = (cf λ)ˇ` needed for the cofinality clause -/

/-- `κ̌` is a cardinal in `V 𝔹` when all ordinals below `κ` have size `≤ ν` (`DistribHyp ν`). -/
theorem cardinal_cof_check {ν : Cardinal.{0}} (hd : Erdos1220Full.CardB.DistribHyp ν β)
    {κ : Cardinal.{0}} (hsmall : ∀ o < κ.ord, o.card ≤ ν) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.cardinal (check (PSet.card_ex κ)) :=
  Erdos1220Full.CardB.sem_cardinal_card_ex_of_distrib hd hsmall

/-- **A ground cofinal check-set of `λ̌` equinumerous with `(cf λ)ˇ`** (no hypothesis on `β`). -/
theorem exists_check_cofinal_eqCard (lam : Cardinal.{0}) :
    ∃ Sg : PSet.{0},
      (⊤ : β) ≤ Flypitch.Erdos1220.Sem.subset (check Sg) (check (PSet.card_ex lam)) ∧
      (⊤ : β) ≤ Flypitch.Erdos1220.Sem.cofinal (check Sg) (check (PSet.card_ex lam)) ∧
      (⊤ : β) ≤ Flypitch.Erdos1220.Sem.eqCard (check Sg) (check (PSet.card_ex lam.ord.cof)) := by
  obtain ⟨Sg, -, hmk, hsub, hcofg, -⟩ := exists_ground_cofinal lam
  have hκ : ZFSet.card (ZFSet.mk (PSet.card_ex lam.ord.cof)) = lam.ord.cof := by
    show ZFSet.card (ZFSet.mk (PSet.ordinalMk lam.ord.cof.ord)) = _
    rw [card_mk_ordinalMk, Cardinal.card_ord]
  refine ⟨Sg, Erdos1220Full.CardB.subsetB_check hsub,
    Erdos1220Full.CardB.sem_cofinal_check hcofg, le_inf ?_ ?_⟩
  · exact Erdos1220Full.CardB.sem_leq_check_of_injects
      (injects_into_of_card_le (by rw [hmk, hκ]))
  · exact Erdos1220Full.CardB.sem_leq_check_of_injects
      (injects_into_of_card_le (by rw [hmk, hκ]))

/-! ### Assembly with the cofinality clause as input -/

/-- The cofinality clause of `Sem.hyp` (to be supplied by `CofClause.lean`). -/
def CofClause (β : Type) [NontrivialCompleteBooleanAlgebra β] (l : bSet β) : Prop :=
  (⊤ : β) ≤ ⨅ d : bSet β, Flypitch.Erdos1220.Sem.cof l d ⟹ Flypitch.Erdos1220.Sem.omegaInacc d

/-- **`⊤ ≤ Sem.hyp λ̌`** from
* (Hcc) `ChainCondition θ β`, `θ` regular, `θ ≤ λ` — for `Sem.cardinal λ̌`;
* (Hdist) `DistribHyp ν β` with `cf λ ≤ ν` — for `Sem.singular λ̌`;
* (HF) countable closure — for `Sem.omegaInacc λ̌`;
* the cofinality clause. -/
theorem hyp_of_cofClause {θ ν : Cardinal.{0}} (hcc : Erdos1220Full.ChainCondition θ β)
    (hθreg : θ.IsRegular) (hd : Erdos1220Full.CardB.DistribHyp ν β) (hF : HF β)
    {lam : Cardinal.{0}} (hH : _root_.Erdos1220.Hypotheses lam) (hθlam : θ ≤ lam)
    (hcofν : lam.ord.cof ≤ ν) (hclause : CofClause β (check (PSet.card_ex lam))) :
    (⊤ : β) ≤ Flypitch.Erdos1220.Sem.hyp (check (PSet.card_ex lam)) := by
  obtain ⟨hsing, hinacc, -⟩ := hH
  unfold Flypitch.Erdos1220.Sem.hyp
  refine le_inf ?_ (le_inf ?_ (le_inf ?_ hclause))
  · exact Erdos1220Full.CardB.sem_cardinal_card_ex_of_chainCondition hcc hθreg hθlam
  · exact singular_card_ex_of_distrib hd hsing hcofν
  · exact omegaInacc_card_ex hF hinacc

/-- (Hcof) implies the cofinality clause (with (HF) and ground `ℵ₀`-inaccessibility of `cf λ`). -/
theorem cofClause_of_HCof (hF : HF β) {lam : Cardinal.{0}}
    (hκ : _root_.Erdos1220.IsOmegaInaccessible lam.ord.cof) (hcof : HCof β lam) :
    CofClause β (check (PSet.card_ex lam)) :=
  cof_omegaInacc_of hF hκ hcof

end Flypitch.Erdos1220.Hyp

#print axioms Flypitch.Erdos1220.Hyp.ord_eq_Ord
#print axioms Flypitch.Erdos1220.Hyp.leq_check_of
#print axioms Flypitch.Erdos1220.Hyp.leq_mono_right
#print axioms Flypitch.Erdos1220.Hyp.leq_check_eq_bot
#print axioms Flypitch.Erdos1220.Hyp.injects_into_of_card_le
#print axioms Flypitch.Erdos1220.Hyp.omegaInacc_card_ex
#print axioms Flypitch.Erdos1220.Hyp.singular_card_ex
#print axioms Flypitch.Erdos1220.Hyp.cof_omegaInacc_of
#print axioms Flypitch.Erdos1220.Hyp.hyp_card_ex
#print axioms Flypitch.Erdos1220.Hyp.hyp_bethWitness
#print axioms Flypitch.Erdos1220.Hyp.exists_ground_cofinal
#print axioms Flypitch.Erdos1220.Hyp.omega_func_inj
#print axioms Flypitch.Erdos1220.Hyp.singular_card_ex_of_distrib
#print axioms Flypitch.Erdos1220.Hyp.cardinal_cof_check
#print axioms Flypitch.Erdos1220.Hyp.exists_check_cofinal_eqCard
#print axioms Flypitch.Erdos1220.Hyp.hyp_of_cofClause
#print axioms Flypitch.Erdos1220.Hyp.cofClause_of_HCof
