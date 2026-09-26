/-
Copyright (c) 2026 Elliot Glazer. Released under Apache 2.0.
Adapted: generic countermodel bridge only; exclude unrelated #501 proof imports.
The final logical bridge for Erdős #1220, following elliotglazer/erdos501
`Erdos501/FOL/Independence.lean` (Apache 2.0, Elliot Glazer) verbatim in structure.
-/
import Erdos1220Full.Statement1220
import Erdos501.FOL.Axioms
import Flypitch4.Completeness

/-!
# From a Boolean-valued countermodel to `¬ (ZFC ⊨ᵇ Erdos1220)`

`not_provable_of_forced`: if some nontrivial complete Boolean algebra `𝔹` forces the negation of
the Flypitch translation `tr Erdos1220` in `V 𝔹` (on a nonzero piece), then the Mathlib-level
target `Erdos1220NotProvable` holds. This is a *reduction* lemma only; the forcing statement is the
remaining mathematical content (Shelah–Stanley §3), not an assumption of the final target.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Fol Erdos501.FOL

namespace Erdos1220.FOL

/-- Flypitch's completeness theorem, contrapositive form: an unprovable sentence has a nonempty
countermodel. -/
lemma exists_model_of_not_sprovable_1220 {φ : sentence L_ZFC} (h : ¬ (_root_.ZFC ⊢ₛ' φ)) :
    ∃ S : Fol.Structure L_ZFC, Nonempty S.carrier ∧ (S ⊨ₜ _root_.ZFC) ∧ ¬ (S ⊨ₘ φ) := by
  rw [Fol.completeness] at h
  by_contra hcon
  apply h
  intro S hne hZ
  by_contra hφ
  exact hcon ⟨S, hne, hZ, hφ⟩

section

variable (S : Fol.Structure L_ZFC)

attribute [local instance] toM

/-- A nonempty Flypitch model of `ZFC` in which the `L`-sentence `φ` fails witnesses
`¬ (ZFC ⊨ᵇ φ)`. -/
theorem not_models_of_countermodel_1220 [Nonempty S.carrier] (hZ : S ⊨ₜ _root_.ZFC) {φ : L.Sentence}
    (hφ : ¬ (S.carrier ⊨ φ)) : ¬ (Erdos501.FOL.ZFC ⊨ᵇ φ) := by
  rw [Theory.models_iff_not_satisfiable]
  intro hsat
  apply hsat
  have : S.carrier ⊨ Erdos501.FOL.ZFC ∪ {φ.not} :=
    Theory.model_union_iff.mpr ⟨toM_models_ZFC S hZ, Theory.model_singleton_iff.mpr hφ⟩
  exact Theory.Model.isSatisfiable S.carrier

end


theorem not_provable_of_forced {𝔹 : Type} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}
    (hΓ : (⊥ : 𝔹) < Γ) (h : Γ ⊩[V 𝔹] (bd_not (tr Erdos1220) : sentence L_ZFC)) :
    Erdos1220NotProvable := by
  have hunp : ¬ (_root_.ZFC ⊢ₛ' tr Erdos1220) :=
    unprovable_of_model_neg (V 𝔹) bSet_models_ZFC hΓ h
  obtain ⟨S, hne, hZ, hφ⟩ := exists_model_of_not_sprovable_1220 hunp
  have := hne
  refine not_models_of_countermodel_1220 S hZ ?_
  rw [realize_sentence_tr]
  exact hφ

end Erdos1220.FOL

#print axioms Erdos1220.FOL.not_provable_of_forced
