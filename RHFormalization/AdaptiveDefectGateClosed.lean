-- SENTINEL: GATE-defect-eps0-closed-v2
import RHFormalization.AdaptiveDefectLocBdd
import RHFormalization.AdaptiveDefectEpsZeroFromLocBdd
import Mathlib

/-!
# THE DEFECT GATE — CLOSED
The eps0 conclusion with no remaining hypotheses: the banked loc_bdd
(L1a→L3b ladder, explicit constant 5/c₀(K) + 1/c₀(K)²) fed into the
banked Montel/eps0 adapter. Type inferred from the adapter application
(v1 guessed a nonexistent conclusion name); #check prints the concluded
statement for the record.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- **The defect gate, closed**: the adapter's conclusion, zero open inputs. -/
def adaptiveGalerkinTransformDefect_eps0 (c : ℝ) :=
  adaptiveGalerkinTransformDefect_eps0_of_loc_bdd c
    (fun K hK hKΩ => adaptiveGalerkinTransformDefect_loc_bdd c K hKΩ hK)

#check @adaptiveGalerkinTransformDefect_eps0
#print axioms adaptiveGalerkinTransformDefect_eps0

end

end RHFormalization
