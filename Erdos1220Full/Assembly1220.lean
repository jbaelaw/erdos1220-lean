import Erdos1220Full.Bridge1220
import Erdos1220Full.Semantics1220
import Erdos1220Full.SentenceF

/-!
# Final assembly interface for `Erdos1220NotProvable`

The headline target follows from three facts about names `l, c` in one Boolean-valued model
`V 𝔹` (`𝔹 : Type`): the hypotheses of #1220 hold for `l`, `c` is a colouring of `[l]²`, and
`c` has neither homogeneous set. This is the interface the forcing construction must meet;
it is *not* the final theorem (which must discharge all three facts for a concrete `𝔹`).
-/

open Fol bSet
open scoped Flypitch

namespace Erdos1220.FOL

theorem not_provable_of_names {𝔹 : Type} [NontrivialCompleteBooleanAlgebra 𝔹]
    (l c : bSet 𝔹) (hh : ⊤ ≤ Flypitch.Erdos1220.Sem.hyp l)
    (hc : ⊤ ≤ Flypitch.Erdos1220.Sem.colouring l c)
    (ha : Flypitch.Erdos1220.Sem.arrow l c ≤ ⊥) : Erdos1220NotProvable := by
  refine not_provable_of_forced (Γ := (⊤ : 𝔹)) bot_lt_top ?_
  rw [tr_Erdos1220]
  exact Flypitch.Erdos1220.forced_not_Erdos1220_f_of l c hh hc (inf_le_right.trans ha)

end Erdos1220.FOL

#print axioms Erdos1220.FOL.not_provable_of_names
