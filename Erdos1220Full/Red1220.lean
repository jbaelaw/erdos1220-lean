import Erdos1220Full.Instance1220
import Erdos1220Full.RedExclusion

/-!
# No red homogeneous set of size `λ = ℶ_{𝔠⁺}` in the concrete model

`red₁`: the first disjunct of `Sem.arrow (check X) cdot₁` is `⊥`.  This instantiates
`RedExclusion.red_exclusion` at the concrete instance of `Instance1220.lean`; all its hypotheses
are ground facts proved here (no use of `Sem.cardinal (check X)` is needed: the small case is
refuted by the `(2^μ)⁺`-chain condition directly).
-/

open Cardinal Set Order Flypitch bSet Lattice
open Erdos1220 Erdos1220.Witness Erdos1220Full.HistoryForcing Erdos1220Full.GenericColouring

namespace Erdos1220.Final

theorem func_of_eq {p : PSet.{0}} {T : Type} {F : T → PSet.{0}} (h : p = PSet.mk T F)
    (a : p.Type) : p.Func a = F (cast (congrArg PSet.Type h) a) := by
  subst h
  rfl

/-- The members of `X` are the von Neumann ordinals of the vertices. -/
theorem X_func (a : X.Type) : X.Func a = PSet.ordinalMk ((eX a).toOrd : Ordinal.{0}) :=
  func_of_eq (PSet.ordinalMk_eq_def lo.{0}) a

theorem mk_X : #X.Type = bethWitness.{0} := by
  rw [← mk_Vtx]
  exact Cardinal.mk_congr eX

theorem hord₁ (a b : X.Type) (h : blockX a < blockX b) : X.Func a ∈ X.Func b := by
  rw [X_func, X_func]
  apply PSet.mk_mem_mk_of_lt
  apply toOrd_lt_of_block_lt
  exact Subtype.coe_lt_coe.mpr (Ordinal.ToType.mk.symm.lt_iff_lt.mpr h)

theorem hθx₁ : Order.succ (2 ^ μ₁) < #X.Type := by
  rw [mk_X]
  have h1 : 2 ^ μ₁ < bethWitness.{0} :=
    bethWitness_isStrongLimit.two_power_lt succ_continuum_lt_bethWitness
  exact lt_of_le_of_lt (Order.succ_le_of_lt (cantor _))
    (bethWitness_isStrongLimit.two_power_lt h1)

theorem block_small (b : Blk.{0}) : #(block ⁻¹' {b} : Set Vtx.{0}) < #Vtx.{0} := by
  have hs : Order.succ (b.toOrd : Ordinal.{0}) < κo.{0} :=
    succ_continuum_ord_isSuccLimit.succ_lt b.toOrd.2
  let w : Vtx.{0} := Ordinal.ToType.mk ⟨(beth (Order.succ (b.toOrd : Ordinal.{0}))).ord, beth_lt_lo hs⟩
  have hsub : (block ⁻¹' {b} : Set Vtx.{0}) ⊆ Iio w := by
    intro v hv
    have hvb : block v = b := hv
    have h1 : ((v.toOrd : Ordinal.{0})) < (beth (Order.succ (blockIdx v))).ord := blockIdx_mem v
    have h2 : blockIdx v = (b.toOrd : Ordinal.{0}) := by rw [← block_toOrd, hvb]
    rw [h2] at h1
    show v < w
    rw [← Ordinal.ToType.mk.symm.lt_iff_lt]
    show v.toOrd < Ordinal.ToType.mk.symm (Ordinal.ToType.mk _)
    rw [OrderIso.symm_apply_apply]
    exact h1
  refine (mk_le_mk_of_subset hsub).trans_lt (Cardinal.mk_Iio_lt w ?_)
  rw [mk_Vtx, Ordinal.type_toType]
  rfl

theorem hblk₁ (b : Blk.{0}) : #(blockX ⁻¹' {b}) < #X.Type := by
  have h : #(blockX ⁻¹' {b}) ≤ #(block ⁻¹' {b} : Set Vtx.{0}) :=
    Cardinal.mk_preimage_of_injective eX _ eX.injective
  rw [mk_X, ← mk_Vtx]
  exact h.trans_lt (block_small b)

/-- **No red homogeneous set of size `λ`** (first disjunct of `Sem.arrow`). -/
theorem red₁ (H : bSet 𝔹₁) :
    Flypitch.Erdos1220.Sem.subset H (check X) ⊓
      (Flypitch.Erdos1220.Sem.eqCard H (check X) ⊓
        Flypitch.Erdos1220.Sem.homog0 cdot₁ H) ≤ ⊥ := by
  have h := Erdos1220Full.RedExclusion.red_exclusion (x := X) (block := blockX) (μ := μ₁)
    (hμ := hμ₁) mk_Blk_le X_inj hord₁ hθx₁ hblk₁ H ⊤
  rwa [top_inf_eq] at h

end Erdos1220.Final

#print axioms Erdos1220.Final.hord₁
#print axioms Erdos1220.Final.hθx₁
#print axioms Erdos1220.Final.hblk₁
#print axioms Erdos1220.Final.red₁
