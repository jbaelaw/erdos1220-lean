import Flypitch4.Zfc
import Flypitch4.ForcingCH

/-!
# Foundation import audit

This module checks the concrete upstream Boolean-valued ZFC framework and the
countable-function reflection result. It does not assert any result for problem
1220. The forcing algebra specific to 1220 still has to be constructed.
-/

#check bSet_models_ZFC
#print axioms bSet_models_ZFC
#check bSet.function_reflect_of_omega_closed
#print axioms bSet.function_reflect_of_omega_closed
