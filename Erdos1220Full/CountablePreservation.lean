/-
The value-decision argument adapts Flypitch4/ForcingCH.lean.
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0; see LICENSE and NOTICE.
Original authors: Jesse Han, Floris van Doorn. Lean 4 port: Ian Klatzco, Claude.
-/

import Flypitch4.ForcingCH

/-!
# No new countable functions from dense countable closure

The upstream function-reflection theorem has an explicit value-decision
interface. We discharge that interface for an arbitrary complete Boolean
algebra with a dense countably closed subset, and prove equality of the full
internal function set with its ground-model check name.
-/

open Flypitch bSet Lattice

universe u

namespace Erdos1220Full

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
variable {D : Set 𝔹}

theorem decide_value_in_dense (hD : DenseOmegaClosed D) (x y : PSet.{u})
    {f : bSet 𝔹} {Γ : 𝔹} (hfunc : Γ ≤ is_func' (check x) (check y) f)
    (hpos : ⊥ < Γ) (i : x.Type) :
    ∃ (j : y.Type) (Δ : 𝔹), ⊥ < Δ ∧ Δ ≤ Γ ∧
      Δ ≤ is_func' (check x) (check y) f ∧
      Δ ≤ pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ f ∧ Δ ∈ D := by
  have htotal : Γ ≤ is_total (check x) (check y) f := is_total_of_is_func' hfunc
  have hmem : Γ ≤ (check (x.Func i)) ∈ᴮ check x := by simp
  have hvalue : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check (x.Func i)) w ∈ᴮ f :=
    (le_inf (htotal.trans (iInf_le _ (check (x.Func i)))) hmem).trans bv_imp_elim
  rw [← @bounded_exists 𝔹 _ (check y) (fun w => pair (check (x.Func i)) w ∈ᴮ f)
    (h_congr := B_ext_pair_mem_right)] at hvalue
  simp only [check_bval_top, top_inf_eq] at hvalue
  have hchoice : Γ ≤ ⨆ j : (check y : bSet 𝔹).type,
      is_func' (check x) (check y) f ⊓
        pair (check (x.Func i)) ((check y).func j) ∈ᴮ f := by
    calc
      Γ ≤ is_func' (check x) (check y) f ⊓
          ⨆ j, pair (check (x.Func i)) ((check y).func j) ∈ᴮ f := le_inf hfunc hvalue
      _ = ⨆ j, is_func' (check x) (check y) f ⊓
          pair (check (x.Func i)) ((check y).func j) ∈ᴮ f := inf_iSup_eq _ _
  obtain ⟨j, Δ, hΔ, hle, hΔD⟩ := collapse_algebra.nonzero_wit'' hD hpos hchoice
  refine ⟨check_cast j, Δ, hΔ, hle.trans inf_le_right,
    hle.trans (inf_le_left.trans inf_le_left), ?_, hΔD⟩
  have h := hle.trans (inf_le_left.trans inf_le_right)
  simpa only [check_func] using h

/-- The decision interface is proved, not passed as an additional premise. -/
theorem reflect_countable_function (hD : DenseOmegaClosed D)
    {y : PSet.{u}} {g : bSet 𝔹} {Γ : 𝔹} (hpos : ⊥ < Γ)
    (hfunc : Γ ≤ is_function bSet.omega (check y) g) :
    ∃ (f : PSet.{u}) (Δ : 𝔹), ⊥ < Δ ∧ Δ ≤ Γ ∧
      Δ ≤ check f =ᴮ g ∧ PSet.is_func PSet.omega y f := by
  exact function_reflect_of_omega_closed hD hpos (is_func'_of_is_function hfunc) hfunc
    (fun x y {f} {Γ'} hfunc hpos i => decide_value_in_dense hD x y hfunc hpos i)

/-- Boolean-algebra density in an arbitrary positive piece suffices for order. -/
theorem le_of_positive_refinements {a b : 𝔹}
    (h : ∀ Γ : 𝔹, ⊥ < Γ → Γ ≤ a →
      ∃ Δ : 𝔹, ⊥ < Δ ∧ Δ ≤ Γ ∧ Δ ≤ b) : a ≤ b := by
  have hzero : a ⊓ bᶜ = ⊥ := by
    by_contra hne
    obtain ⟨Δ, hpos, hΔ, hb⟩ := h (a ⊓ bᶜ) (bot_lt_iff_ne_bot.mpr hne) inf_le_left
    have hbot : Δ ≤ b ⊓ bᶜ := le_inf hb (hΔ.trans inf_le_right)
    rw [inf_compl_eq_bot] at hbot
    exact hpos.not_ge hbot
  calc
    a = a ⊓ b ⊔ a ⊓ bᶜ := (sup_inf_inf_compl (x := a) (y := b)).symm
    _ = a ⊓ b := by rw [hzero, sup_bot_eq]
    _ ≤ b := inf_le_right

/-- Dense countable closure preserves the whole set of countable functions
into any ground-model set, as a Boolean-valued equality. -/
theorem check_countable_functions_eq (hD : DenseOmegaClosed D) (y : PSet.{u})
    (Γ : 𝔹) :
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
  obtain ⟨f, Δ', hpos', hle, heq, hf⟩ := reflect_countable_function hD hpos hfunc
  refine ⟨Δ', hpos', hle, ?_⟩
  exact bv_rw' (bv_symm heq)
    (ϕ := fun z => z ∈ᴮ check (PSet.functions PSet.omega y))
    (h_congr := B_ext_mem_left)
    (H_new := check_mem ((PSet.mem_functions_iff f).mpr hf))

end Erdos1220Full

#print axioms Erdos1220Full.reflect_countable_function
#print axioms Erdos1220Full.check_countable_functions_eq
