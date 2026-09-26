import Erdos1220Full.Instance1220

/-!
# Concrete facts about the witness used by the exclusion arguments
-/

open Cardinal Ordinal Order
open Erdos1220.Witness

namespace Erdos1220.Final

theorem X_func (a : X.Type) : X.Func a = PSet.ordinalMk ((eX a).toOrd : Ordinal) := by
  have key : ∀ (P : PSet.{0}) (hP : P = ⟨lo.{0}.ToType, fun b => PSet.ordinalMk b.toOrd.val⟩)
      (a : P.Type), P.Func a = PSet.ordinalMk ((cast (congrArg PSet.Type hP) a).toOrd : Ordinal) := by
    intro P hP a
    subst hP
    rfl
  exact key X (PSet.ordinalMk_eq_def _) a

/-- Membership between vertices is the ordinal order. -/
theorem X_mem_iff (a b : X.Type) :
    X.Func a ∈ X.Func b ↔ ((eX a).toOrd : Ordinal) < (eX b).toOrd := by
  rw [X_func, X_func]
  constructor
  · intro h
    obtain ⟨c, hc, heq⟩ := PSet.mem_ordinalMk_iff.mp h
    rw [PSet.eq_of_mk_equiv heq]
    exact hc
  · exact PSet.mk_mem_mk_of_lt

/-- Blocks are intervals: a smaller block index gives membership. -/
theorem X_mem_of_block_lt {a b : X.Type}
    (h : ((blockX a).toOrd : Ordinal) < (blockX b).toOrd) : X.Func a ∈ X.Func b :=
  (X_mem_iff a b).mpr (toOrd_lt_of_block_lt h)

/-- `θ = (2^μ)⁺ < λ`. -/
theorem theta_lt_lam : Order.succ ((2 : Cardinal.{0}) ^ μ₁) < bethWitness.{0} := by
  have h1 : (2 : Cardinal.{0}) ^ μ₁ < bethWitness :=
    bethWitness_isStrongLimit.two_power_lt succ_continuum_lt_bethWitness
  exact bethWitness_isStrongLimit.isSuccLimit.succ_lt h1

/-- Each block has size `< λ`. -/
theorem mk_block_lt (i : Blk.{0}) : #{v : X.Type // blockX v = i} < bethWitness.{0} := by
  set j : Ordinal.{0} := (i.toOrd : Ordinal)
  have hj : j < κo.{0} := i.toOrd.2
  have hsj : Order.succ j < κo.{0} := succ_continuum_ord_isSuccLimit.succ_lt hj
  have hlt : ∀ v : {v : X.Type // blockX v = i},
      ((eX v.1).toOrd : Ordinal) < (beth (Order.succ j)).ord := by
    intro v
    have := blockIdx_mem (eX v.1)
    have hb : blockIdx (eX v.1) = j := by
      rw [← block_toOrd]; exact congrArg (fun t : Blk.{0} => (t.toOrd : Ordinal)) v.2
    rw [hb] at this; exact this
  let f : {v : X.Type // blockX v = i} → (beth (Order.succ j)).ord.ToType :=
    fun v => Ordinal.ToType.mk ⟨((eX v.1).toOrd : Ordinal), hlt v⟩
  have hinj : Function.Injective f := by
    intro v w h
    have h1 := congrArg (fun t => ((Ordinal.ToType.mk.symm t : Set.Iio _) : Ordinal)) h
    simp only [f, OrderIso.symm_apply_apply] at h1
    apply Subtype.ext
    apply eX.injective
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext h1)
  calc #{v : X.Type // blockX v = i} ≤ #((beth (Order.succ j)).ord.ToType) :=
        Cardinal.mk_le_of_injective hinj
    _ = beth (Order.succ j) := by simp
    _ < bethWitness.{0} := by
        rw [bethWitness]
        exact beth_strictMono (lt_of_lt_of_le hsj le_rfl)

end Erdos1220.Final

#print axioms Erdos1220.Final.X_mem_iff
#print axioms Erdos1220.Final.X_mem_of_block_lt
#print axioms Erdos1220.Final.theta_lt_lam
#print axioms Erdos1220.Final.mk_block_lt
