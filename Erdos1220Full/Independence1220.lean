import Erdos1220Full.CofInstance1220
import Erdos1220Full.Red1220
import Erdos1220Full.BlueFinal1220
import Erdos1220Full.ArrowFinal
import Erdos1220Full.Assembly1220
import Erdos1220Full.Faithful1220

/-!
# Erdős #1220: the universal statement is not provable in ZFC

The concrete Boolean-valued model `V 𝔹₁` (Shelah–Stanley history forcing over the witness
`λ = ℶ_{𝔠⁺}`, blocks = beth intervals) satisfies, for `l = λ̌` and the generic colouring `ċ`:
the hypotheses of #1220 (`hyp₁`), `ċ` is a colouring (`colouring₁`), there is no red
homogeneous set of size `λ` (`red₁`) and no blue homogeneous set of size `ℵ₁` (`blue₁`).
Hence `¬ Erdos1220` is forced, and by soundness/completeness `¬ (ZFC ⊨ᵇ Erdos1220)`.

This is **non-provability only** (a negative answer is consistent with ZFC); the positive
consistency direction (full independence) is not claimed here.
-/

open Fol bSet
open scoped Flypitch

namespace Erdos1220.FOL

open Erdos1220.Final

/-- **Erdős #1220 is not provable in ZFC.** -/
theorem erdos1220_not_provable : ¬ (Erdos501.FOL.ZFC ⊨ᵇ Erdos1220.FOL.Erdos1220) :=
  not_provable_of_names (check X) cdot₁ hyp₁ colouring₁ arrow₁

end Erdos1220.FOL

#print axioms Erdos1220.FOL.erdos1220_not_provable
#print axioms Erdos1220.FOL.erdos1220_sentence_faithful
