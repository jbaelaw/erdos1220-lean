import Erdos1220Full.Red1220
import Erdos1220Full.BlueFinal1220
import Erdos1220Full.ArrowAssembly

open bSet

namespace Erdos1220.Final

/-- No homogeneous set of either kind for the generic colouring on `λ̌`. -/
theorem arrow₁ : Flypitch.Erdos1220.Sem.arrow (check X) cdot₁ ≤ ⊥ :=
  Flypitch.Erdos1220.arrow_le_bot (fun H => red₁ H) (fun w H => blue₁ w H)

end Erdos1220.Final

#print axioms Erdos1220.Final.arrow₁
