/-
The regular-open algebra uses Flypitch4/RegularOpenAlgebra.lean. The final
function-equality argument in `check_eq_of_forall_pair` is adapted from
`bSet.function_reflect_of_omega_closed` in Flypitch4/ForcingCH.lean.
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0; see LICENSE and NOTICE.
Original authors: Jesse Han, Floris van Doorn. Lean 4 port: Ian Klatzco, Claude.
-/

import Flypitch4.ForcingCH
import Erdos1220Full.ChainPreservation
import Erdos1220Full.CountablePreservation

/-!
# The regular-open algebra of an arbitrary forcing preorder

Convention (Kunen): for conditions `p q : P`, `q ≤ p` means that `q` is
*stronger* than (extends) `p`.

For an arbitrary preorder `P` (in `Type u`) we give `P` the lower-set
(Alexandrov) topology, whose open sets are the downward closed sets, and take
`RO P := Flypitch.RegularOpens (PosetSpace P)`. This is Flypitch's own
regular-open complete Boolean algebra, so for `Nonempty P` it is a
`NontrivialCompleteBooleanAlgebra` and `bSet (RO P)` is available.

* `emb p` is the regular-open hull of the cone `Iic p`; `x ∈ emb p` iff every
  extension of `x` is compatible with `p`.
* `emb` is monotone, positive, dense, and sends incompatible conditions to
  disjoint elements (and conversely).
* An antichain bound `κ` on `P` gives `ChainCondition κ (RO P)`.
* Countable closure:
  - for separative `P` whose decreasing `ℕ`-chains have greatest lower bounds,
    `Set.range emb` is literally Flypitch's `DenseOmegaClosed` subset;
  - for an arbitrary countably closed `P`, the range of `emb` need not be
    `DenseOmegaClosed` in Flypitch's exact-infimum sense, so we prove the
    consequences directly: countably many simultaneous decisions below any
    positive element, reflection of `ω`-sequences into ground-model sets, and
    the Boolean equality `check (ω → y) = (ω → check y)`.
-/

open Set Cardinal Flypitch Flypitch.Regular bSet Lattice

universe u

namespace Erdos1220Full

/-! ## Order-theoretic notions (stronger = smaller) -/

section PosetNotions

variable {P : Type u} [Preorder P]

/-- Two conditions are compatible when they have a common extension. -/
def Compatible (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q

theorem Compatible.symm {p q : P} (h : Compatible p q) : Compatible q p :=
  let ⟨r, h₁, h₂⟩ := h; ⟨r, h₂, h₁⟩

theorem compatible_refl (p : P) : Compatible p p := ⟨p, le_rfl, le_rfl⟩

/-- `κ`-chain condition of the preorder: every family of size at least `κ`
contains two distinct indices with compatible conditions. -/
def AntichainBound (κ : Cardinal.{u}) (P : Type u) [Preorder P] : Prop :=
  ∀ (ι : Type u) (p : ι → P), κ ≤ #ι → ∃ i j, i ≠ j ∧ Compatible (p i) (p j)

/-- Every descending `ℕ`-sequence (in forcing strength) has a lower bound. -/
def CountablyClosed (P : Type u) [Preorder P] : Prop :=
  ∀ s : ℕ → P, (∀ n, s (n + 1) ≤ s n) → ∃ q, ∀ n, q ≤ s n

/-- Separativity: if `p` does not extend `q`, some extension of `p` is
incompatible with `q`. -/
def Separative (P : Type u) [Preorder P] : Prop :=
  ∀ p q : P, ¬ p ≤ q → ∃ r, r ≤ p ∧ ¬ Compatible r q

/-- Every descending `ℕ`-sequence has a greatest lower bound. -/
def HasCountableChainInfima (P : Type u) [Preorder P] : Prop :=
  ∀ s : ℕ → P, (∀ n, s (n + 1) ≤ s n) →
    ∃ q, (∀ n, q ≤ s n) ∧ ∀ r, (∀ n, r ≤ s n) → r ≤ q

theorem HasCountableChainInfima.countablyClosed {P : Type u} [Preorder P]
    (h : HasCountableChainInfima P) : CountablyClosed P := fun s hs =>
  let ⟨q, hq, _⟩ := h s hs; ⟨q, hq⟩

end PosetNotions

/-! ## The lower-set topology -/

/-- A copy of `P` carrying the lower-set topology (so that an existing
topology on `P` is never picked up). -/
def PosetSpace (P : Type u) : Type u := P

namespace PosetSpace

variable {P : Type u} [Preorder P]

instance instPreorder : Preorder (PosetSpace P) := inferInstanceAs (Preorder P)

instance instNonempty [h : Nonempty P] : Nonempty (PosetSpace P) := h

/-- The identity map into the topologized copy. -/
abbrev of (p : P) : PosetSpace P := p

instance topology : TopologicalSpace (PosetSpace P) where
  IsOpen s := IsLowerSet s
  isOpen_univ := isLowerSet_univ
  isOpen_inter _ _ hs ht := hs.inter ht
  isOpen_sUnion _ h := isLowerSet_sUnion h

theorem isOpen_iff {s : Set (PosetSpace P)} : IsOpen s ↔ IsLowerSet s := Iff.rfl

theorem mem_closure_iff' {S : Set (PosetSpace P)} {x : PosetSpace P} :
    x ∈ closure S ↔ ∃ y ∈ S, y ≤ x := by
  rw [_root_.mem_closure_iff]
  constructor
  · intro h
    obtain ⟨y, hy, hyS⟩ := h (Iic x) (isOpen_iff.mpr (isLowerSet_Iic x)) (Set.mem_Iic.mpr le_rfl)
    exact ⟨y, hyS, hy⟩
  · rintro ⟨y, hyS, hyx⟩ o ho hxo
    exact ⟨y, (isOpen_iff.mp ho) hyx hxo, hyS⟩

theorem mem_perp_iff' {S : Set (PosetSpace P)} {x : PosetSpace P} :
    x ∈ Sᵖ ↔ ∀ y ≤ x, y ∉ S := by
  show x ∉ closure S ↔ _
  rw [mem_closure_iff']
  constructor
  · intro h y hy hyS
    exact h ⟨y, hyS, hy⟩
  · rintro h ⟨y, hyS, hy⟩
    exact h y hy hyS

theorem mem_pp_iff {S : Set (PosetSpace P)} {x : PosetSpace P} :
    x ∈ Sᵖᵖ ↔ ∀ y ≤ x, ∃ z ≤ y, z ∈ S := by
  rw [mem_perp_iff']
  constructor
  · intro h y hy
    by_contra hne
    push Not at hne
    exact h y hy (mem_perp_iff'.mpr hne)
  · intro h y hy hyp
    obtain ⟨z, hz, hzS⟩ := h y hy
    exact (mem_perp_iff'.mp hyp) z hz hzS

end PosetSpace

/-! ## The algebra `RO P` and the dense embedding -/

/-- The regular-open algebra of the forcing preorder `P`. -/
abbrev RO (P : Type u) [Preorder P] : Type u := RegularOpens (PosetSpace P)

section Embedding

variable {P : Type u} [Preorder P]

/-- The canonical map: the regular-open hull of the cone below `p`. -/
def emb (p : P) : RO P := ⟨(Iic (PosetSpace.of p))ᵖᵖ, isRegularOpen_p_p⟩

theorem RO.le_iff_subset {a b : RO P} : a ≤ b ↔ a.val ⊆ b.val := Iff.rfl

theorem RO.isLowerSet (b : RO P) : IsLowerSet b.val :=
  PosetSpace.isOpen_iff.mp (isOpen_of_isRegularOpen b.property)

theorem mem_emb {p : P} {x : PosetSpace P} :
    x ∈ (emb p).val ↔ ∀ y ≤ x, Compatible (P := P) y p := by
  show x ∈ (Iic (PosetSpace.of p))ᵖᵖ ↔ _
  rw [PosetSpace.mem_pp_iff]
  exact Iff.rfl

theorem mem_emb_self (p : P) : PosetSpace.of p ∈ (emb p).val :=
  mem_emb.mpr fun y hy => ⟨y, le_rfl, hy⟩

/-- `emb p ≤ b` exactly when `p` itself lies in the regular open `b`. -/
theorem emb_le_iff {p : P} {b : RO P} : emb p ≤ b ↔ PosetSpace.of p ∈ b.val := by
  constructor
  · intro h
    exact RO.le_iff_subset.mp h (mem_emb_self p)
  · intro hp
    rw [RO.le_iff_subset]
    show (Iic (PosetSpace.of p))ᵖᵖ ⊆ b.val
    rw [← isRegularOpen_eq_p_p b.property]
    exact p_p_mono fun x hx => b.isLowerSet hx hp

theorem emb_mono {p q : P} (h : q ≤ p) : emb q ≤ emb p :=
  RO.le_iff_subset.mpr (p_p_mono (Iic_subset_Iic.mpr h))

theorem compatible_of_mem_emb {p : P} {x : PosetSpace P} (hx : x ∈ (emb p).val) :
    Compatible (P := P) x p :=
  mem_emb.mp hx x le_rfl

theorem emb_le_emb_iff {p q : P} : emb q ≤ emb p ↔ ∀ r ≤ q, Compatible r p := by
  rw [emb_le_iff, mem_emb]
  exact Iff.rfl

theorem compatible_of_emb_le {p q : P} (h : emb q ≤ emb p) : Compatible q p :=
  emb_le_emb_iff.mp h q le_rfl

variable [Nonempty P]

theorem emb_pos (p : P) : ⊥ < emb p :=
  RegularOpens.bot_lt_iff.mpr ⟨PosetSpace.of p, mem_emb_self p⟩

/-- Density: every positive element is above the image of some condition. -/
theorem exists_emb_le {b : RO P} (hb : ⊥ < b) : ∃ p : P, emb p ≤ b := by
  obtain ⟨x, hx⟩ := RegularOpens.bot_lt_iff.mp hb
  exact ⟨x, emb_le_iff.mpr hx⟩

theorem compatible_iff_bot_lt_emb_inf {p q : P} : Compatible p q ↔ ⊥ < emb p ⊓ emb q := by
  constructor
  · rintro ⟨r, hrp, hrq⟩
    exact lt_of_lt_of_le (emb_pos r) (le_inf (emb_mono hrp) (emb_mono hrq))
  · intro h
    obtain ⟨x, hxp, hxq⟩ := RegularOpens.bot_lt_iff.mp h
    obtain ⟨r, hrx, hrp⟩ := compatible_of_mem_emb hxp
    have hrq : PosetSpace.of r ∈ (emb q).val := (emb q).isLowerSet hrx hxq
    obtain ⟨s, hsr, hsq⟩ := compatible_of_mem_emb hrq
    exact ⟨s, le_trans hsr hrp, hsq⟩

/-- Incompatible conditions are sent to disjoint elements. -/
theorem emb_inf_eq_bot_of_not_compatible {p q : P} (h : ¬ Compatible p q) :
    emb p ⊓ emb q = ⊥ := by
  by_contra hne
  exact h (compatible_iff_bot_lt_emb_inf.mpr (bot_lt_iff_ne_bot.mpr hne))

/-- Every element is the join of the conditions below it. -/
theorem eq_iSup_emb (b : RO P) : b = ⨆ p : {p : P // emb p ≤ b}, emb p.1 := by
  apply le_antisymm
  · apply le_of_positive_refinements
    intro Γ hΓ hΓb
    obtain ⟨p, hp⟩ := exists_emb_le hΓ
    exact ⟨emb p, emb_pos p, hp, le_iSup (fun q : {p : P // emb p ≤ b} => emb q.1)
      ⟨p, hp.trans hΓb⟩⟩
  · exact iSup_le fun p => p.2

end Embedding

/-! ## Chain condition transfer -/

section Chain

variable {P : Type u} [Preorder P] [Nonempty P]

theorem chainCondition_RO {κ : Cardinal.{u}} (h : AntichainBound κ P) :
    ChainCondition κ (RO P) := by
  intro ι a hpos hdisj
  choose p hp using fun i => exists_emb_le (hpos i)
  by_contra hlt
  obtain ⟨i, j, hij, hc⟩ := h ι p (not_lt.mp hlt)
  have h₁ : ⊥ < emb (p i) ⊓ emb (p j) := compatible_iff_bot_lt_emb_inf.mp hc
  have h₂ : emb (p i) ⊓ emb (p j) ≤ ⊥ := (inf_le_inf (hp i) (hp j)).trans (hdisj i j hij)
  exact (not_le_of_gt h₁) h₂

end Chain

/-! ## Countable closure, exact Flypitch interface (separative case) -/

section Separative

variable {P : Type u} [Preorder P] [Nonempty P]

omit [Nonempty P] in
theorem mem_emb_iff_le (hsep : Separative P) {p : P} {x : PosetSpace P} :
    x ∈ (emb p).val ↔ x ≤ PosetSpace.of p := by
  constructor
  · intro hx
    by_contra hn
    obtain ⟨r, hr, hinc⟩ := hsep x p hn
    exact hinc (mem_emb.mp hx r hr)
  · intro hx
    exact in_p_p_of_open (PosetSpace.isOpen_iff.mpr (isLowerSet_Iic _)) hx

omit [Nonempty P] in
theorem emb_le_emb_iff_le (hsep : Separative P) {p q : P} : emb q ≤ emb p ↔ q ≤ p := by
  rw [emb_le_iff, mem_emb_iff_le hsep]
  exact Iff.rfl

/-- For a separative preorder whose descending `ℕ`-chains have greatest lower
bounds, the image of the preorder is a dense `ω`-closed subset in exactly
Flypitch's sense. -/
theorem denseOmegaClosed_range_emb (hsep : Separative P) (hinf : HasCountableChainInfima P) :
    DenseOmegaClosed (Set.range (emb : P → RO P)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨p, hp⟩
    exact (emb_pos p).ne' hp
  · intro b hb
    obtain ⟨p, hp⟩ := exists_emb_le hb
    exact ⟨emb p, ⟨p, rfl⟩, hp⟩
  · intro s hs _ hdec
    choose p hp using hs
    have hsp : s = fun n => emb (p n) := funext fun n => (hp n).symm
    subst hsp
    have hpdec : ∀ n, p (n + 1) ≤ p n := fun n => (emb_le_emb_iff_le hsep).mp (hdec n)
    obtain ⟨q, hq, hglb⟩ := hinf p hpdec
    refine ⟨q, ?_⟩
    apply RegularOpens.ext
    show (Iic (PosetSpace.of q))ᵖᵖ = (⨅ n, emb (p n)).val
    rw [RegularOpens.fst_iInf]
    have hI : (⋂ n, (emb (p n)).val) = Iic (PosetSpace.of q) := by
      ext x
      simp only [Set.mem_iInter, mem_emb_iff_le hsep, Set.mem_Iic]
      exact ⟨fun hx => hglb x hx, fun hx n => le_trans hx (hq n)⟩
    rw [hI]

/-- Consequently the internal set of countable functions is the ground one. -/
theorem check_countable_functions_eq_RO_of_separative (hsep : Separative P)
    (hinf : HasCountableChainInfima P) (y : PSet.{u}) (Γ : RO P) :
    Γ ≤ check (PSet.functions PSet.omega y) =ᴮ functions bSet.omega (check y) :=
  check_countable_functions_eq (denseOmegaClosed_range_emb hsep hinf) y Γ

end Separative

/-! ## Countable closure, arbitrary countably closed preorder -/

section Pointwise

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- A Boolean-valued function `ω → check y` that is forced (on `Δ`) to agree
with a ground-model sequence at every natural number is forced to be that
ground-model function. -/
theorem check_eq_of_forall_pair {y : PSet.{u}} {g : bSet 𝔹} {Δ : 𝔹}
    (fr : ℕ → y.Type) (H_function : Δ ≤ is_function bSet.omega (check y) g)
    (hpair : ∀ n : ℕ,
      Δ ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func (fr n))) ∈ᴮ g) :
    ∃ f : PSet.{u}, Δ ≤ check f =ᴮ g ∧ PSet.is_func PSet.omega y f := by
  let fr' : PSet.omega.Type → y.Type := fun k => fr k.down
  let f' : PSet.{u} :=
    PSet.function_mk.mk (x := PSet.omega) (fun (k : PSet.omega.Type) => y.Func (fr' k))
      (fun i j heqv => by
        have hij : i = j := PSet.omega_inj heqv
        subst hij; exact PSet.Equiv.refl _)
  have f'_is_func : PSet.is_func PSet.omega y f' :=
    PSet.function_mk.mk_is_func _ (fun i => PSet.func_mem y (fr' i))
  have iInf_fBᵦ_pair : ∀ n, Δ ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func (fr' ⟨n⟩))) ∈ᴮ g :=
    fun n => hpair n
  have f'_mem : ∀ (i : PSet.omega.Type),
      (⊤ : 𝔹) ≤ pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ (check f' : bSet 𝔹) := by
    intro i
    have hmem : PSet.pSet_pair (PSet.omega.Func i) (y.Func (fr' i)) ∈ f' :=
      PSet.function_mk.mk_mem
    have h : (⊤ : 𝔹) ≤ check (PSet.pSet_pair (PSet.omega.Func i) (y.Func (fr' i))) ∈ᴮ check f' :=
      check_mem hmem
    exact subst_congr_mem_left' (check_pset_pair (Γ := (⊤ : 𝔹))) h
  have hΓ'_f'_is_function : Δ ≤ is_function (check PSet.omega) (check y) (check f') :=
    le_trans le_top (check_is_func f'_is_func)
  have hΓ'_g_is_function : Δ ≤ is_function bSet.omega (check y) g :=
    H_function
  have hΓ'_f'_is_func' : Δ ≤ is_func' (check PSet.omega) (check y) (check f') :=
    hΓ'_f'_is_function.trans inf_le_left
  have hΓ'_g_is_func' : Δ ≤ is_func' bSet.omega (check y) g :=
    hΓ'_g_is_function.trans inf_le_left
  have Γ'_le_eq : Δ ≤ check f' =ᴮ g := by
    apply mem_ext
    · -- ⊆ direction: ∀ z, z ∈ check f' ⟹ z ∈ g
      apply le_iInf; intro z; rw [← deduction]
      have hz_in_f' := inf_le_right (a := Δ) (b := z ∈ᴮ check f')
      rw [mem_unfold] at hz_in_f'
      have hz_in_prod : Δ ⊓ z ∈ᴮ check f' ≤ z ∈ᴮ bSet.prod (check PSet.omega) (check y) :=
        mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_f'_is_function)) inf_le_right
      rw [mem_unfold] at hz_in_prod
      have hctx_le : Δ ⊓ z ∈ᴮ check f' ≤
          ⨆ (ij : (bSet.prod (check PSet.omega) (check y)).type),
          Δ ⊓ z ∈ᴮ check f' ⊓
          ((bSet.prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check PSet.omega) (check y)).func ij) := by
        rw [← inf_iSup_eq]
        apply le_inf
        · exact le_refl _
        · exact hz_in_prod
      apply hctx_le.trans
      apply iSup_le; intro ij
      have hstep : Δ ⊓ z ∈ᴮ check f' ⊓
          ((bSet.prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check PSet.omega) (check y)).func ij) ≤
          z ∈ᴮ g := by
        have hbval : (bSet.prod (check PSet.omega) (check y)).bval ij = ⊤ := prod_check_bval
        rw [hbval, top_inf_eq]
        let i : PSet.omega.Type := check_cast ij.1
        let j : y.Type := check_cast ij.2
        have hfunc : (bSet.prod (check PSet.omega) (check y)).func ij =
            pair (check (PSet.omega.Func i)) (check (y.Func j)) := by
          simp only [prod_func, check_func]
          rfl
        rw [hfunc]
        have hpair_eq : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
          bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ check f')
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
        have hf'_fri : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ check f' :=
          le_trans le_top (f'_mem i)
        have h_eq : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            check (y.Func j) =ᴮ check (y.Func (fr' i)) :=
          eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_f'_is_func')
            bv_refl hpair_eq hf'_fri
        have hg_fri : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
          le_trans (inf_le_left.trans inf_le_left) (iInf_fBᵦ_pair i.down)
        have hg_j : Δ ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ g :=
          bv_rw' h_eq (ϕ := fun z => pair (check (PSet.omega.Func i)) z ∈ᴮ g)
            (h_congr := B_ext_pair_mem_right) (H_new := hg_fri)
        exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ g)
          (h_congr := B_ext_mem_left) (H_new := hg_j)
      exact hstep
    · -- ⊇ direction: ∀ z, z ∈ g ⟹ z ∈ check f'
      apply le_iInf; intro z; rw [← deduction]
      have hz_in_prod : Δ ⊓ z ∈ᴮ g ≤ z ∈ᴮ bSet.prod (check PSet.omega) (check y) :=
        mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_g_is_function)) inf_le_right
      conv at hz_in_prod => rw [show z ∈ᴮ bSet.prod (check PSet.omega) (check y) =
          ⨆ (i : (bSet.prod (check PSet.omega) (check y)).type),
          (bSet.prod (check PSet.omega) (check y)).bval i ⊓ z =ᴮ (bSet.prod (check PSet.omega) (check y)).func i
          from mem_unfold]
      have hctx_le : Δ ⊓ z ∈ᴮ g ≤
          ⨆ (ij : (bSet.prod (check PSet.omega) (check y)).type),
          Δ ⊓ z ∈ᴮ g ⊓
          ((bSet.prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check PSet.omega) (check y)).func ij) := by
        have heq : (⨆ (ij : (bSet.prod (check PSet.omega) (check y)).type),
              Δ ⊓ z ∈ᴮ g ⊓
              ((bSet.prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check PSet.omega) (check y)).func ij)) =
              Δ ⊓ z ∈ᴮ g ⊓
              ⨆ (ij : (bSet.prod (check PSet.omega) (check y)).type),
              (bSet.prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check PSet.omega) (check y)).func ij :=
          (inf_iSup_eq _ _).symm
        rw [heq]
        refine le_inf le_rfl ?_
        have : Δ ⊓ z ∈ᴮ g ≤
            ⨆ (ij : (bSet.prod (check PSet.omega) (check y)).type),
            (bSet.prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check PSet.omega) (check y)).func ij :=
          hz_in_prod
        exact this
      apply hctx_le.trans
      apply iSup_le; intro ij
      have hstep : Δ ⊓ z ∈ᴮ g ⊓
          ((bSet.prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (bSet.prod (check PSet.omega) (check y)).func ij) ≤
          z ∈ᴮ check f' := by
        have hbval : (bSet.prod (check PSet.omega) (check y)).bval ij = ⊤ := prod_check_bval
        rw [hbval, top_inf_eq]
        let i : PSet.omega.Type := check_cast ij.1
        let j : y.Type := check_cast ij.2
        have hfunc : (bSet.prod (check PSet.omega) (check y)).func ij =
            pair (check (PSet.omega.Func i)) (check (y.Func j)) := by
          simp only [prod_func, check_func]
          rfl
        rw [hfunc]
        have hpair_eq : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ g :=
          bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ g)
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
        have hg_fri : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
          le_trans (inf_le_left.trans inf_le_left) (iInf_fBᵦ_pair i.down)
        have h_eq : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            check (y.Func j) =ᴮ check (y.Func (fr' i)) :=
          eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_g_is_func')
            bv_refl hpair_eq hg_fri
        have hf'_fri : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ check f' :=
          le_trans le_top (f'_mem i)
        have hf'_j : Δ ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
          bv_rw' h_eq (ϕ := fun z => pair (check (PSet.omega.Func i)) z ∈ᴮ check f')
            (h_congr := B_ext_pair_mem_right) (H_new := hf'_fri)
        exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ check f')
          (h_congr := B_ext_mem_left) (H_new := hf'_j)
      exact hstep
  exact ⟨f', Γ'_le_eq, f'_is_func⟩

end Pointwise

section Closed

variable {P : Type u} [Preorder P] [Nonempty P]

/-- **External `(ω, ∞)`-distributivity.** Below a positive `Γ`, countably many
choices can be made simultaneously by a single condition. The chain is built
in `P` itself, so no separativity is needed. -/
theorem exists_forall_of_countablyClosed (hP : CountablyClosed P) {Γ : RO P}
    (hΓ : ⊥ < Γ) {ι : ℕ → Type*} (φ : ∀ n, ι n → RO P)
    (hφ : ∀ n (Γ' : RO P), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ n i) :
    ∃ (q : P) (c : ∀ n, ι n), emb q ≤ Γ ∧ ∀ n, emb q ≤ φ n (c n) := by
  have hstep : ∀ (n : ℕ) (p : {p : P // emb p ≤ Γ}),
      ∃ (i : ι n) (s : {p : P // emb p ≤ Γ}), s.1 ≤ p.1 ∧ emb s.1 ≤ φ n i := by
    intro n p
    obtain ⟨i, hi⟩ := hφ n (emb p.1) (emb_pos p.1) p.2
    obtain ⟨r, hr⟩ := exists_emb_le hi
    obtain ⟨s, hsr, hsp⟩ := compatible_of_emb_le (hr.trans inf_le_left)
    exact ⟨i, ⟨s, (emb_mono hsp).trans p.2⟩, hsp,
      (emb_mono hsr).trans (hr.trans inf_le_right)⟩
  choose I S hSle hSφ using hstep
  obtain ⟨p₀, hp₀⟩ := exists_emb_le hΓ
  let chain : ℕ → {p : P // emb p ≤ Γ} := fun n =>
    Nat.rec (motive := fun _ => {p : P // emb p ≤ Γ}) ⟨p₀, hp₀⟩ (fun k c => S k c) n
  have hchain : ∀ n, chain (n + 1) = S n (chain n) := fun _ => rfl
  obtain ⟨q, hq⟩ := hP (fun n => (chain n).1) (fun n => by
    show (chain (n + 1)).1 ≤ (chain n).1
    rw [hchain]
    exact hSle n (chain n))
  refine ⟨q, fun n => I n (chain n), (emb_mono (hq 0)).trans (chain 0).2, fun n => ?_⟩
  have h₁ : emb q ≤ emb (chain (n + 1)).1 := emb_mono (hq (n + 1))
  rw [hchain] at h₁
  exact h₁.trans (hSφ n (chain n))

/-- Countably closed forcing adds no new `ω`-sequences of ground-model
elements: every forced function `ω → check y` is, on a positive piece below
any given positive `Γ`, equal to a ground-model function. -/
theorem reflect_countable_function_RO (hP : CountablyClosed P) {y : PSet.{u}}
    {g : bSet (RO P)} {Γ : RO P} (hpos : ⊥ < Γ)
    (hfunc : Γ ≤ is_function bSet.omega (check y) g) :
    ∃ (f : PSet.{u}) (Δ : RO P), ⊥ < Δ ∧ Δ ≤ Γ ∧
      Δ ≤ check f =ᴮ g ∧ PSet.is_func PSet.omega y f := by
  have hsup : ∀ i : PSet.omega.Type, Γ ≤ ⨆ j : (check y : bSet (RO P)).type,
      pair (check (PSet.omega.Func i)) (check (y.Func (check_cast j))) ∈ᴮ g := by
    intro i
    have htotal : Γ ≤ is_total (check PSet.omega) (check y) g :=
      is_total_of_is_func' (is_func'_of_is_function hfunc)
    have hmem : Γ ≤ (check (PSet.omega.Func i) : bSet (RO P)) ∈ᴮ check PSet.omega := by
      rw [check_mem'']
      exact le_top
    have hvalue : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check (PSet.omega.Func i)) w ∈ᴮ g :=
      (le_inf (htotal.trans (iInf_le _ (check (PSet.omega.Func i)))) hmem).trans bv_imp_elim
    rw [← @bounded_exists (RO P) _ (check y)
      (fun w => pair (check (PSet.omega.Func i)) w ∈ᴮ g)
      (h_congr := B_ext_pair_mem_right)] at hvalue
    simpa only [check_bval_top, top_inf_eq, check_func] using hvalue
  obtain ⟨q, c, hqΓ, hqc⟩ := exists_forall_of_countablyClosed hP hpos
    (ι := fun _ => (check y : bSet (RO P)).type)
    (fun n j => pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func (check_cast j))) ∈ᴮ g)
    (fun n Γ' hΓ' hle => nonzero_inf_of_nonzero_le_supr hΓ' (hle.trans (hsup ⟨n⟩)))
  obtain ⟨f, hf, hfis⟩ := check_eq_of_forall_pair (fun n => check_cast (c n))
    (hqΓ.trans hfunc) hqc
  exact ⟨f, emb q, emb_pos q, hqΓ, hf, hfis⟩

/-- Countably closed forcing: the internal set of functions `ω → check y` is
the check name of the ground-model set of such functions. -/
theorem check_countable_functions_eq_RO (hP : CountablyClosed P) (y : PSet.{u})
    (Γ : RO P) :
    Γ ≤ check (PSet.functions PSet.omega y) =ᴮ functions bSet.omega (check y) := by
  refine subset_ext check_functions_subset_functions ?_
  rw [subset_unfold']
  apply le_iInf
  intro g
  rw [← deduction]
  apply le_of_positive_refinements
  intro Δ hpos hΔ
  have hfunc : Δ ≤ is_function bSet.omega (check y) g :=
    mem_functions_iff.mp (hΔ.trans inf_le_right)
  obtain ⟨f, Δ', hpos', hle, heq, hf⟩ := reflect_countable_function_RO hP hpos hfunc
  refine ⟨Δ', hpos', hle, ?_⟩
  exact bv_rw' (bv_symm heq)
    (ϕ := fun z => z ∈ᴮ check (PSet.functions PSet.omega y))
    (h_congr := B_ext_mem_left)
    (H_new := check_mem ((PSet.mem_functions_iff f).mpr hf))

end Closed

end Erdos1220Full

#print axioms Erdos1220Full.emb_le_iff
#print axioms Erdos1220Full.emb_le_emb_iff
#print axioms Erdos1220Full.emb_pos
#print axioms Erdos1220Full.exists_emb_le
#print axioms Erdos1220Full.compatible_iff_bot_lt_emb_inf
#print axioms Erdos1220Full.emb_inf_eq_bot_of_not_compatible
#print axioms Erdos1220Full.eq_iSup_emb
#print axioms Erdos1220Full.chainCondition_RO
#print axioms Erdos1220Full.denseOmegaClosed_range_emb
#print axioms Erdos1220Full.check_countable_functions_eq_RO_of_separative
#print axioms Erdos1220Full.check_eq_of_forall_pair
#print axioms Erdos1220Full.exists_forall_of_countablyClosed
#print axioms Erdos1220Full.reflect_countable_function_RO
#print axioms Erdos1220Full.check_countable_functions_eq_RO
