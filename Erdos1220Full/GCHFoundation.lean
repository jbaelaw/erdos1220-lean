import ConstructibleUniverse.SetTheory.ZFC.Constructible.CHRelativeConsistency

/-!
# Constructible-model foundation audit

This is the existing concrete model of ZFC + GCH, not yet the positive
partition theorem for problem 1220. The language and semantic bridges to the
forcing development still require explicit proofs.
-/

#check FirstOrder.Language.Theory.ZFCGCH_isSatisfiable
#print axioms FirstOrder.Language.Theory.ZFCGCH_isSatisfiable
#check Constructible.ContinuumFormula.modelsGCH_lCarrier
#print axioms Constructible.ContinuumFormula.modelsGCH_lCarrier
