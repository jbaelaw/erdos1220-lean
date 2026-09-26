import Erdos1220Full.CofInstance1220
import Erdos1220Full.BlueFinal1220
import Erdos1220Full.InstanceFacts

/-!
# Contract check: `Erdos1220.Final.hyp₁`

`hyp₁ : (⊤ : 𝔹₁) ≤ Sem.hyp (check X)` is proved in `CofInstance1220.lean` from
`HypInstance1220.lean` (cardinal/singular/`ℵ₀`-inaccessible clauses and the `κ̌` facts) and
`CofClause.lean` (the cofinality clause).  This file imports it together with `BlueFinal1220`
(whose `cc₁` no longer collides: the Hyp-side chain condition is `ccHyp₁`) and checks the exact
statement of the contract.
-/

open Flypitch bSet

example : (⊤ : Erdos1220.Final.𝔹₁) ≤ Flypitch.Erdos1220.Sem.hyp (check Erdos1220.Final.X) :=
  Erdos1220.Final.hyp₁

#print axioms Erdos1220.Final.hyp₁
