/-
The function-equality argument in `check_eq_of_forall_pair_general` is adapted
from `bSet.function_reflect_of_omega_closed` in Flypitch4/ForcingCH.lean.
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0; see LICENSE and NOTICE.
Original authors: Jesse Han, Floris van Doorn. Lean 4 port: Ian Klatzco, Claude.
-/

import Erdos1220.WeakOrder
import Erdos1220.BlockInitial
import Erdos1220Full.PosetAlgebra

/-!
# The historical forcing and its distributivity

`HP V I block μ hμ` is the preorder of block-preserving histories with
`q ≤ p :⇔ WeakExtends p q` (`q` is stronger). Its Boolean completion is
`RO (HP V I block μ hμ)` from `PosetAlgebra.lean`.

Distributivity is proved inside the preorder, from the explicit player-II
strategy `BPHistory.strategic_closure`: player I, at stage `α`, moves to a
weak extension of II's position whose image lies below some `φ j i` for the
index `j` scheduled at stage `α`. No separativity is used.

Consequently no new functions from a small ground set into a ground set are
added (`reflect_function_HP`, `check_functions_eq_HP`).

Universe note: histories live in `Type (u + 1)`, so the algebra is in
`Type (u + 1)` and the relevant pre-sets are `PSet.{u + 1}`.
-/

open Cardinal Set Order Flypitch bSet Lattice

universe u v w

namespace Erdos1220Full

/-! ## Function equality for an arbitrary ground domain -/

section Pointwise

variable {𝔹 : Type v} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- A Boolean-valued function `check x → check y` which is forced on `Δ` to
agree with a ground-model map at every element of `x` equals, on `Δ`, the
check name of that ground function. The elements of `x` must be pairwise
non-equivalent (e.g. `x` an ordinal or `PSet.card_ex κ`). -/
theorem check_eq_of_forall_pair_general {x y : PSet.{v}} {g : bSet 𝔹} {Δ : 𝔹}
    (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    (fr : x.Type → y.Type) (H_function : Δ ≤ is_function (check x) (check y) g)
    (hpair : ∀ i, Δ ≤ pair (check (x.Func i)) (check (y.Func (fr i))) ∈ᴮ g) :
    ∃ f : PSet.{v}, Δ ≤ check f =ᴮ g ∧ PSet.is_func x y f := by
  let fr' : x.Type → y.Type := fr
  let f' : PSet.{v} :=
    PSet.function_mk.mk (x := x) (fun (k : x.Type) => y.Func (fr' k))
      (fun i j heqv => by
        have hij : i = j := hx i j heqv
        subst hij; exact PSet.Equiv.refl _)
  have f'_is_func : PSet.is_func x y f' :=
    PSet.function_mk.mk_is_func _ (fun i => PSet.func_mem y (fr' i))
  have iInf_fBᵦ_pair : ∀ i, Δ ≤ pair (check (x.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
    fun i => hpair i
  have f'_mem : ∀ (i : x.Type),
      (⊤ : 𝔹) ≤ pair (check (x.Func i)) (check (y.Func (fr' i))) ∈ᴮ (check f' : bSet 𝔹) := by
    intro i
    have hmem : PSet.pSet_pair (x.Func i) (y.Func (fr' i)) ∈ f' :=
      PSet.function_mk.mk_mem
    have h : (⊤ : 𝔹) ≤ check (PSet.pSet_pair (x.Func i) (y.Func (fr' i))) ∈ᴮ check f' :=
      check_mem hmem
    exact subst_congr_mem_left' (check_pset_pair (Γ := (⊤ : 𝔹))) h
  have hΓ'_f'_is_function : Δ ≤ is_function (check x) (check y) (check f') :=
    le_trans le_top (check_is_func f'_is_func)
  have hΓ'_g_is_function : Δ ≤ is_function (check x) (check y) g :=
    H_function
  have hΓ'_f'_is_func' : Δ ≤ is_func' (check x) (check y) (check f') :=
    hΓ'_f'_is_function.trans inf_le_left
  have hΓ'_g_is_func' : Δ ≤ is_func' (check x) (check y) g :=
    hΓ'_g_is_function.trans inf_le_left
  have Γ'_le_eq : Δ ≤ check f' =ᴮ g := by
    apply mem_ext
    · -- ⊆ direction: ∀ z, z ∈ check f' ⟹ z ∈ g
      apply le_iInf; intro z; rw [← deduction]
      have hz_in_f' := inf_le_right (a := Δ) (b := z ∈ᴮ check f')
      rw [mem_unfold] at hz_in_f'
      have hz_in_prod : Δ ⊓ z ∈ᴮ check f' ≤ z ∈ᴮ bSet.prod (check x) (check y) :=
        mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_f'_is_function)) inf_le_right
      rw [mem_unfold] at hz_in_prod
      have hctx_le : Δ ⊓ z ∈ᴮ check f' ≤
          ⨆ (ij : (bSet.prod (check x) (check y)).type),
          Δ ⊓ z ∈ᴮ check f' ⊓
          ((bSet.prod (check x) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check x) (check y)).func ij) := by
        rw [← inf_iSup_eq]
        apply le_inf
        · exact le_refl _
        · exact hz_in_prod
      apply hctx_le.trans
      apply iSup_le; intro ij
      have hstep : Δ ⊓ z ∈ᴮ check f' ⊓
          ((bSet.prod (check x) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check x) (check y)).func ij) ≤
          z ∈ᴮ g := by
        have hbval : (bSet.prod (check x) (check y)).bval ij = ⊤ := prod_check_bval
        rw [hbval, top_inf_eq]
        let i : x.Type := check_cast ij.1
        let j : y.Type := check_cast ij.2
        have hfunc : (bSet.prod (check x) (check y)).func ij =
            pair (check (x.Func i)) (check (y.Func j)) := by
          simp only [prod_func, check_func]
          rfl
        rw [hfunc]
        have hpair_eq : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
          bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ check f')
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
        have hf'_fri : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            pair (check (x.Func i)) (check (y.Func (fr' i))) ∈ᴮ check f' :=
          le_trans le_top (f'_mem i)
        have h_eq : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            check (y.Func j) =ᴮ check (y.Func (fr' i)) :=
          eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_f'_is_func')
            bv_refl hpair_eq hf'_fri
        have hg_fri : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            pair (check (x.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
          le_trans (inf_le_left.trans inf_le_left) (iInf_fBᵦ_pair i)
        have hg_j : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ g :=
          bv_rw' h_eq (ϕ := fun z => pair (check (x.Func i)) z ∈ᴮ g)
            (h_congr := B_ext_pair_mem_right) (H_new := hg_fri)
        exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ g)
          (h_congr := B_ext_mem_left) (H_new := hg_j)
      exact hstep
    · -- ⊇ direction: ∀ z, z ∈ g ⟹ z ∈ check f'
      apply le_iInf; intro z; rw [← deduction]
      have hz_in_prod : Δ ⊓ z ∈ᴮ g ≤ z ∈ᴮ bSet.prod (check x) (check y) :=
        mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_g_is_function)) inf_le_right
      conv at hz_in_prod => rw [show z ∈ᴮ bSet.prod (check x) (check y) =
          ⨆ (i : (bSet.prod (check x) (check y)).type),
          (bSet.prod (check x) (check y)).bval i ⊓ z =ᴮ (bSet.prod (check x) (check y)).func i
          from mem_unfold]
      have hctx_le : Δ ⊓ z ∈ᴮ g ≤
          ⨆ (ij : (bSet.prod (check x) (check y)).type),
          Δ ⊓ z ∈ᴮ g ⊓
          ((bSet.prod (check x) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check x) (check y)).func ij) := by
        have heq : (⨆ (ij : (bSet.prod (check x) (check y)).type),
              Δ ⊓ z ∈ᴮ g ⊓
              ((bSet.prod (check x) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check x) (check y)).func ij)) =
              Δ ⊓ z ∈ᴮ g ⊓
              ⨆ (ij : (bSet.prod (check x) (check y)).type),
              (bSet.prod (check x) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check x) (check y)).func ij :=
          (inf_iSup_eq _ _).symm
        rw [heq]
        refine le_inf le_rfl ?_
        have : Δ ⊓ z ∈ᴮ g ≤
            ⨆ (ij : (bSet.prod (check x) (check y)).type),
            (bSet.prod (check x) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check x) (check y)).func ij :=
          hz_in_prod
        exact this
      apply hctx_le.trans
      apply iSup_le; intro ij
      have hstep : Δ ⊓ z ∈ᴮ g ⊓
          ((bSet.prod (check x) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check x) (check y)).func ij) ≤
          z ∈ᴮ check f' := by
        have hbval : (bSet.prod (check x) (check y)).bval ij = ⊤ := prod_check_bval
        rw [hbval, top_inf_eq]
        let i : x.Type := check_cast ij.1
        let j : y.Type := check_cast ij.2
        have hfunc : (bSet.prod (check x) (check y)).func ij =
            pair (check (x.Func i)) (check (y.Func j)) := by
          simp only [prod_func, check_func]
          rfl
        rw [hfunc]
        have hpair_eq : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ g :=
          bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ g)
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
        have hg_fri : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            pair (check (x.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
          le_trans (inf_le_left.trans inf_le_left) (iInf_fBᵦ_pair i)
        have h_eq : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            check (y.Func j) =ᴮ check (y.Func (fr' i)) :=
          eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_g_is_func')
            bv_refl hpair_eq hg_fri
        have hf'_fri : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            pair (check (x.Func i)) (check (y.Func (fr' i))) ∈ᴮ check f' :=
          le_trans le_top (f'_mem i)
        have hf'_j : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
            pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
          bv_rw' h_eq (ϕ := fun z => pair (check (x.Func i)) z ∈ᴮ check f')
            (h_congr := B_ext_pair_mem_right) (H_new := hf'_fri)
        exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ check f')
          (h_congr := B_ext_mem_left) (H_new := hf'_j)
      exact hstep

  exact ⟨f', Γ'_le_eq, f'_is_func⟩

end Pointwise

namespace HistoryForcing

open Erdos1220 Erdos1220.BPHistory

variable {V I : Type u} {block : V → I} {μ : Cardinal.{u}} {hμ : ℵ₀ ≤ μ}

/-! ## The forcing preorder -/

/-- Block-preserving histories as forcing conditions. -/
def HP (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Type (u + 1) :=
  BPHistory V I block μ hμ

/-- `q ≤ p` iff `q` weakly extends `p` (`q` is stronger). -/
instance instPreorder : Preorder (HP V I block μ hμ) where
  le p q := WeakExtends (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ) q p
  le_refl p := WeakExtends.refl p
  le_trans _ _ _ hab hbc := hbc.trans hab

theorem le_iff {p q : HP V I block μ hμ} :
    p ≤ q ↔ WeakExtends (V := V) (I := I) (block := block) (μ := μ) (hμ := hμ) q p :=
  Iff.rfl

/-- The forcing is nonempty: the one-point-per-block initial history. -/
theorem nonempty [Nontrivial I] (rep : I → V) (hrep : ∀ i, block (rep i) = i)
    (hI : #I ≤ μ) : Nonempty (HP V I block μ hμ) :=
  ⟨(show BPHistory V I block μ hμ from
    ⟨History.ofBlockSection (hμ := hμ) rep hrep hI,
      History.ofBlockSection_blockPreserving rep hrep hI⟩)⟩

/-- The Boolean completion of the historical forcing. -/
abbrev Alg (V I : Type u) (block : V → I) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Type (u + 1) :=
  RO (HP V I block μ hμ)

/-! ## Distributivity from strategic closure -/

section Distributive

variable [Nonempty (HP V I block μ hμ)]

/-- **Distributivity.** Let `J` be scheduled injectively at stages below some
`ρ < μ⁺`. Below any positive `Γ`, one condition decides a choice `c j` for
every `j : J` simultaneously. -/
theorem exists_forall_of_schedule {J : Type w} (e : J → Ordinal.{u})
    (he : Function.Injective e) {ρ : Ordinal.{u}} (hρ : ρ < (Order.succ μ).ord)
    (heρ : ∀ j, e j < ρ) {Γ : Alg V I block μ hμ} (hΓ : ⊥ < Γ) {ι : J → Type*}
    (φ : ∀ j, ι j → Alg V I block μ hμ)
    (hφ : ∀ j (Γ' : Alg V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ j i) :
    ∃ (q : HP V I block μ hμ) (c : ∀ j, ι j), emb q ≤ Γ ∧ ∀ j, emb q ≤ φ j (c j) := by
  classical
  obtain ⟨p₀, hp₀⟩ := exists_emb_le hΓ
  have hnext : ∀ (j : J) (G : HP V I block μ hμ), emb G ≤ Γ →
      ∃ K : HP V I block μ hμ, K ≤ G ∧ ∃ i, emb K ≤ φ j i := by
    intro j G hG
    obtain ⟨i, hi⟩ := hφ j (emb G) (emb_pos G) hG
    obtain ⟨r, hr⟩ := exists_emb_le hi
    obtain ⟨s, hsr, hsG⟩ := compatible_of_emb_le (hr.trans inf_le_left)
    exact ⟨s, hsG, i, (emb_mono hsr).trans (hr.trans inf_le_right)⟩
  let Good : Ordinal.{u} → BPHistory V I block μ hμ → BPHistory V I block μ hμ → Prop :=
    fun α G K => WeakExtends G K ∧
      ∀ j, e j = α → ∃ i, emb (P := HP V I block μ hμ) K ≤ φ j i
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
  obtain ⟨h0, hchain, -, hweak⟩ :=
    strategic_closure (show BPHistory V I block μ hμ from p₀) moveI hmoveI
  have hbelow : ∀ α, α < (Order.succ μ).ord →
      emb (P := HP V I block μ hμ) (play (show BPHistory V I block μ hμ from p₀) moveI α) ≤ Γ := by
    intro α hα
    have hpure := hchain 0 α bot_le hα
    rw [h0] at hpure
    exact (emb_mono (le_iff.mpr (WeakExtends.of_pure hpure))).trans hp₀
  have hmove : ∀ j, ∃ i, emb (P := HP V I block μ hμ)
      (moveI (e j) fun γ _ => play (show BPHistory V I block μ hμ from p₀) moveI γ) ≤ φ j i := by
    intro j
    have hlt : e j < (Order.succ μ).ord := (heρ j).trans hρ
    have hex : ∃ K, Good (e j) (play (show BPHistory V I block μ hμ from p₀) moveI (e j)) K := by
      obtain ⟨K, hK, i, hi⟩ := hnext j _ (hbelow _ hlt)
      refine ⟨K, hK, fun j' hj' => ?_⟩
      obtain rfl := he hj'
      exact ⟨i, hi⟩
    have hm : (moveI (e j) fun γ _ => play (show BPHistory V I block μ hμ from p₀) moveI γ) =
        Classical.choose hex := dif_pos hex
    rw [hm]
    exact (Classical.choose_spec hex).2 j rfl
  choose c hc using hmove
  refine ⟨play (show BPHistory V I block μ hμ from p₀) moveI ρ, c, hbelow ρ hρ, fun j => ?_⟩
  exact (emb_mono (le_iff.mpr (hweak (e j) ρ (heρ j) hρ))).trans (hc j)

/-- Distributivity for sequences indexed by the ordinals below `ρ < μ⁺`. -/
theorem exists_forall_ordinal {ρ : Ordinal.{u}} (hρ : ρ < (Order.succ μ).ord)
    {Γ : Alg V I block μ hμ} (hΓ : ⊥ < Γ) {ι : Ordinal.{u} → Type*}
    (φ : ∀ α, ι α → Alg V I block μ hμ)
    (hφ : ∀ α, α < ρ → ∀ (Γ' : Alg V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ →
      ∃ i, ⊥ < Γ' ⊓ φ α i) :
    ∃ (q : HP V I block μ hμ) (c : ∀ α : Set.Iio ρ, ι α.1), emb q ≤ Γ ∧
      ∀ α : Set.Iio ρ, emb q ≤ φ α.1 (c α) :=
  exists_forall_of_schedule (J := Set.Iio ρ) Subtype.val Subtype.val_injective hρ
    (fun α => α.2) hΓ (fun α => φ α.1) (fun α => hφ α.1 α.2)

/-- Distributivity for any index type of cardinality at most `μ`. -/
theorem exists_forall_of_card_le {J : Type w}
    (hJ : Cardinal.lift.{u} #J ≤ Cardinal.lift.{w} μ)
    {Γ : Alg V I block μ hμ} (hΓ : ⊥ < Γ) {ι : J → Type*}
    (φ : ∀ j, ι j → Alg V I block μ hμ)
    (hφ : ∀ j (Γ' : Alg V I block μ hμ), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ j i) :
    ∃ (q : HP V I block μ hμ) (c : ∀ j, ι j), emb q ≤ Γ ∧ ∀ j, emb q ≤ φ j (c j) := by
  have hJ' : Cardinal.lift.{u} #J ≤ Cardinal.lift.{w} #(μ.ord.ToType) := by
    rwa [Cardinal.mk_toType, Cardinal.card_ord]
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hJ'
  let e : J → Ordinal.{u} := fun j => (Ordinal.ToType.mk.symm (f j)).1
  have he : Function.Injective e := by
    intro j k hjk
    exact f.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext hjk))
  exact exists_forall_of_schedule e he (Cardinal.ord_lt_ord.mpr (Order.lt_succ μ))
    (fun j => (Ordinal.ToType.mk.symm (f j)).2) hΓ φ hφ

/-! ## No new small functions -/

/-- Every forced function from a small ground set `x` (pairwise non-equivalent
elements, `#x ≤ μ`) into a ground set `y` is, on a positive piece below any
positive `Γ`, equal to a ground-model function. -/
theorem reflect_function_HP {x y : PSet.{u + 1}}
    (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    (hxμ : Cardinal.lift.{u} #x.Type ≤ Cardinal.lift.{u + 1} μ)
    {g : bSet (Alg V I block μ hμ)} {Γ : Alg V I block μ hμ} (hpos : ⊥ < Γ)
    (hfunc : Γ ≤ is_function (check x) (check y) g) :
    ∃ (f : PSet.{u + 1}) (Δ : Alg V I block μ hμ), ⊥ < Δ ∧ Δ ≤ Γ ∧
      Δ ≤ check f =ᴮ g ∧ PSet.is_func x y f := by
  have hsup : ∀ i : x.Type, Γ ≤ ⨆ j : (check y : bSet (Alg V I block μ hμ)).type,
      pair (check (x.Func i)) (check (y.Func (check_cast j))) ∈ᴮ g := by
    intro i
    have htotal : Γ ≤ is_total (check x) (check y) g :=
      is_total_of_is_func' (is_func'_of_is_function hfunc)
    have hmem : Γ ≤ (check (x.Func i) : bSet (Alg V I block μ hμ)) ∈ᴮ check x := by
      rw [check_mem'']
      exact le_top
    have hvalue : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check (x.Func i)) w ∈ᴮ g :=
      (le_inf (htotal.trans (iInf_le _ (check (x.Func i)))) hmem).trans bv_imp_elim
    rw [← @bounded_exists (Alg V I block μ hμ) _ (check y)
      (fun w => pair (check (x.Func i)) w ∈ᴮ g)
      (h_congr := B_ext_pair_mem_right)] at hvalue
    simpa only [check_bval_top, top_inf_eq, check_func] using hvalue
  obtain ⟨q, c, hqΓ, hqc⟩ := exists_forall_of_card_le hxμ hpos
    (ι := fun _ => (check y : bSet (Alg V I block μ hμ)).type)
    (fun i j => pair (check (x.Func i)) (check (y.Func (check_cast j))) ∈ᴮ g)
    (fun i Γ' hΓ' hle => nonzero_inf_of_nonzero_le_supr hΓ' (hle.trans (hsup i)))
  obtain ⟨f, hf, hfis⟩ := check_eq_of_forall_pair_general hx (fun i => check_cast (c i))
    (hqΓ.trans hfunc) hqc
  exact ⟨f, emb q, emb_pos q, hqΓ, hf, hfis⟩

/-- The internal set of functions `check x → check y` is the check name of
the ground-model set of such functions. -/
theorem check_functions_eq_HP {x y : PSet.{u + 1}}
    (hx : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → i = j)
    (hxμ : Cardinal.lift.{u} #x.Type ≤ Cardinal.lift.{u + 1} μ)
    (Γ : Alg V I block μ hμ) :
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
  obtain ⟨f, Δ', hpos', hle, heq, hf⟩ := reflect_function_HP hx hxμ hpos hfunc
  refine ⟨Δ', hpos', hle, ?_⟩
  exact bv_rw' (bv_symm heq)
    (ϕ := fun z => z ∈ᴮ check (PSet.functions x y))
    (h_congr := B_ext_mem_left)
    (H_new := check_mem ((PSet.mem_functions_iff f).mpr hf))

end Distributive

end HistoryForcing

end Erdos1220Full

#print axioms Erdos1220Full.check_eq_of_forall_pair_general
#print axioms Erdos1220Full.HistoryForcing.nonempty
#print axioms Erdos1220Full.HistoryForcing.exists_forall_of_schedule
#print axioms Erdos1220Full.HistoryForcing.exists_forall_ordinal
#print axioms Erdos1220Full.HistoryForcing.exists_forall_of_card_le
#print axioms Erdos1220Full.HistoryForcing.reflect_function_HP
#print axioms Erdos1220Full.HistoryForcing.check_functions_eq_HP
