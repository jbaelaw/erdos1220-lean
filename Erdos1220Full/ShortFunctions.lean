/-
Generalization of `function_reflect_of_omega_closed` (Flypitch4/ForcingCH.lean,
src/forcing_CH.lean:216-348) from `ω` to an arbitrary ground set `x`.
Copyright of the original: 2019 The Flypitch Project (Jesse Han, Floris van Doorn),
Lean 4 port Ian Klatzco; Apache 2.0 (see NOTICE).
-/
import Erdos1220Full.Distributive

/-!
# No new short functions from a pure-extension strategy

If a complete Boolean algebra carries a `PureClosure` of length `θ`, then every
Boolean-valued function from the check name of a ground set `x`, indexed below
`θ`, into a check name is (locally) equal to the check name of a ground function.
-/

open Flypitch bSet Lattice

universe u

namespace Erdos1220Full

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- A graph in the ground model that is locally contained in `g` is locally equal to `g`. -/
theorem check_eq_of_graph {x y : PSet.{u}} (fr : x.Type → y.Type)
    (H_ext : ∀ i j, PSet.Equiv (x.Func i) (x.Func j) → PSet.Equiv (y.Func (fr i)) (y.Func (fr j)))
    {g : bSet 𝔹} {Γ' : 𝔹}
    (hΓ'_g_is_function : Γ' ≤ is_function (check x) (check y) g)
    (hpair : ∀ i, Γ' ≤ pair (check (x.Func i)) (check (y.Func (fr i))) ∈ᴮ g) :
    Γ' ≤ check (PSet.function_mk.mk (x := x) (fun i => y.Func (fr i)) H_ext) =ᴮ g := by
  set f' := PSet.function_mk.mk (x := x) (fun i => y.Func (fr i)) H_ext with hf'
  have f'_is_func : PSet.is_func x y f' :=
    PSet.function_mk.mk_is_func _ (fun i => PSet.func_mem y (fr i))
  have f'_mem : ∀ (i : x.Type),
      (⊤ : 𝔹) ≤ pair (check (x.Func i)) (check (y.Func (fr i))) ∈ᴮ (check f' : bSet 𝔹) := by
    intro i
    have hmem : PSet.pSet_pair (x.Func i) (y.Func (fr i)) ∈ f' :=
      PSet.function_mk.mk_mem
    have h : (⊤ : 𝔹) ≤ check (PSet.pSet_pair (x.Func i) (y.Func (fr i))) ∈ᴮ check f' :=
      check_mem hmem
    exact subst_congr_mem_left' (check_pset_pair (Γ := (⊤ : 𝔹))) h
  have hΓ'_f'_is_function : Γ' ≤ is_function (check x) (check y) (check f') :=
    le_trans le_top (check_is_func f'_is_func)
  have hΓ'_f'_is_func' : Γ' ≤ is_func' (check x) (check y) (check f') :=
    hΓ'_f'_is_function.trans inf_le_left
  have hΓ'_g_is_func' : Γ' ≤ is_func' (check x) (check y) g :=
    hΓ'_g_is_function.trans inf_le_left
  apply mem_ext
  · -- ⊆ direction: ∀ z, z ∈ check f' ⟹ z ∈ g
    apply le_iInf; intro z; rw [← deduction]
    have hz_in_f' := inf_le_right (a := Γ') (b := z ∈ᴮ check f')
    rw [mem_unfold] at hz_in_f'
    have hz_in_prod : Γ' ⊓ z ∈ᴮ check f' ≤ z ∈ᴮ prod (check x) (check y) :=
      mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_f'_is_function)) inf_le_right
    rw [mem_unfold] at hz_in_prod
    have hctx_le : Γ' ⊓ z ∈ᴮ check f' ≤
        ⨆ (ij : (prod (check x) (check y)).type),
        Γ' ⊓ z ∈ᴮ check f' ⊓
        ((prod (check x) (check y)).bval ij ⊓ z =ᴮ (prod (check x) (check y)).func ij) := by
      rw [← inf_iSup_eq]
      apply le_inf
      · exact le_refl _
      · exact hz_in_prod
    apply hctx_le.trans
    apply iSup_le; intro ij
    have hstep : Γ' ⊓ z ∈ᴮ check f' ⊓
        ((prod (check x) (check y)).bval ij ⊓ z =ᴮ (prod (check x) (check y)).func ij) ≤
        z ∈ᴮ g := by
      have hbval : (prod (check x) (check y)).bval ij = ⊤ := prod_check_bval
      rw [hbval, top_inf_eq]
      let i : x.Type := check_cast ij.1
      let j : y.Type := check_cast ij.2
      have hfunc : (prod (check x) (check y)).func ij =
          pair (check (x.Func i)) (check (y.Func j)) := by
        simp only [prod_func, check_func]
        rfl
      rw [hfunc]
      have hpair_eq : Γ' ⊓ z ∈ᴮ check f' ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
        bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ check f')
          (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
      have hf'_fri : Γ' ⊓ z ∈ᴮ check f' ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          pair (check (x.Func i)) (check (y.Func (fr i))) ∈ᴮ check f' :=
        le_trans le_top (f'_mem i)
      have h_eq : Γ' ⊓ z ∈ᴮ check f' ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          check (y.Func j) =ᴮ check (y.Func (fr i)) :=
        eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_f'_is_func')
          bv_refl hpair_eq hf'_fri
      have hg_fri : Γ' ⊓ z ∈ᴮ check f' ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          pair (check (x.Func i)) (check (y.Func (fr i))) ∈ᴮ g :=
        le_trans (inf_le_left.trans inf_le_left) (hpair i)
      have hg_j : Γ' ⊓ z ∈ᴮ check f' ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ g :=
        bv_rw' h_eq (ϕ := fun z => pair (check (x.Func i)) z ∈ᴮ g)
          (h_congr := B_ext_pair_mem_right) (H_new := hg_fri)
      exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ g)
        (h_congr := B_ext_mem_left) (H_new := hg_j)
    exact hstep
  · -- ⊇ direction: ∀ z, z ∈ g ⟹ z ∈ check f'
    apply le_iInf; intro z; rw [← deduction]
    have hz_in_prod : Γ' ⊓ z ∈ᴮ g ≤ z ∈ᴮ prod (check x) (check y) :=
      mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_g_is_function)) inf_le_right
    conv at hz_in_prod => rw [show z ∈ᴮ prod (check x) (check y) =
        ⨆ (i : (prod (check x) (check y)).type),
        (prod (check x) (check y)).bval i ⊓ z =ᴮ (prod (check x) (check y)).func i
        from mem_unfold]
    have hctx_le : Γ' ⊓ z ∈ᴮ g ≤
        ⨆ (ij : (prod (check x) (check y)).type),
        Γ' ⊓ z ∈ᴮ g ⊓
        ((prod (check x) (check y)).bval ij ⊓ z =ᴮ (prod (check x) (check y)).func ij) := by
      have heq : (⨆ (ij : (prod (check x) (check y)).type),
            Γ' ⊓ z ∈ᴮ g ⊓
            ((prod (check x) (check y)).bval ij ⊓ z =ᴮ (prod (check x) (check y)).func ij)) =
            Γ' ⊓ z ∈ᴮ g ⊓
            ⨆ (ij : (prod (check x) (check y)).type),
            (prod (check x) (check y)).bval ij ⊓ z =ᴮ (prod (check x) (check y)).func ij :=
        (inf_iSup_eq _ _).symm
      rw [heq]
      refine le_inf le_rfl ?_
      have : Γ' ⊓ z ∈ᴮ g ≤
          ⨆ (ij : (prod (check x) (check y)).type),
          (prod (check x) (check y)).bval ij ⊓ z =ᴮ (prod (check x) (check y)).func ij :=
        hz_in_prod
      exact this
    apply hctx_le.trans
    apply iSup_le; intro ij
    have hstep : Γ' ⊓ z ∈ᴮ g ⊓
        ((prod (check x) (check y)).bval ij ⊓ z =ᴮ (prod (check x) (check y)).func ij) ≤
        z ∈ᴮ check f' := by
      have hbval : (prod (check x) (check y)).bval ij = ⊤ := prod_check_bval
      rw [hbval, top_inf_eq]
      let i : x.Type := check_cast ij.1
      let j : y.Type := check_cast ij.2
      have hfunc : (prod (check x) (check y)).func ij =
          pair (check (x.Func i)) (check (y.Func j)) := by
        simp only [prod_func, check_func]
        rfl
      rw [hfunc]
      have hpair_eq : Γ' ⊓ z ∈ᴮ g ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ g :=
        bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ g)
          (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
      have hg_fri : Γ' ⊓ z ∈ᴮ g ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          pair (check (x.Func i)) (check (y.Func (fr i))) ∈ᴮ g :=
        le_trans (inf_le_left.trans inf_le_left) (hpair i)
      have h_eq : Γ' ⊓ z ∈ᴮ g ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          check (y.Func j) =ᴮ check (y.Func (fr i)) :=
        eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_g_is_func')
          bv_refl hpair_eq hg_fri
      have hf'_fri : Γ' ⊓ z ∈ᴮ g ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          pair (check (x.Func i)) (check (y.Func (fr i))) ∈ᴮ check f' :=
        le_trans le_top (f'_mem i)
      have hf'_j : Γ' ⊓ z ∈ᴮ g ⊓
          z =ᴮ pair (check (x.Func i)) (check (y.Func j)) ≤
          pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
        bv_rw' h_eq (ϕ := fun z => pair (check (x.Func i)) z ∈ᴮ check f')
          (h_congr := B_ext_pair_mem_right) (H_new := hf'_fri)
      exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ check f')
        (h_congr := B_ext_mem_left) (H_new := hf'_j)
    exact hstep

end Erdos1220Full

#print axioms Erdos1220Full.check_eq_of_graph
