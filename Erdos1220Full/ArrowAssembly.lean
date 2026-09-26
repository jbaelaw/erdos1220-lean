import Erdos1220Full.Semantics1220

/-!
# `Sem.arrow ≤ ⊥` from the two exclusions
-/

open Fol bSet
open scoped Flypitch

namespace Flypitch.Erdos1220

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

theorem arrow_le_bot {l c : bSet β}
    (hred : ∀ H : bSet β, Sem.subset H l ⊓ (Sem.eqCard H l ⊓ Sem.homog0 c H) ≤ ⊥)
    (hblue : ∀ w H : bSet β,
      Sem.omega1 w ⊓ (Sem.subset H l ⊓ (Sem.eqCard H w ⊓ Sem.homog1 c H)) ≤ ⊥) :
    Sem.arrow l c ≤ ⊥ := by
  unfold Sem.arrow
  refine sup_le (iSup_le fun H => hred H) (iSup_le fun w => ?_)
  rw [inf_iSup_eq]
  exact iSup_le fun H => hblue w H

end Flypitch.Erdos1220

#print axioms Flypitch.Erdos1220.arrow_le_bot
