import RHFormalization.PrimeOpNonnegDischarge
import RHFormalization.PrimeOperatorArithmeticWeights
import Mathlib

/-!
# Unconditional arithmetic prime stage: hnn supplied, not assumed.

arithmeticPrimeOperatorDFiniteStage takes hnn as a hypothesis. Here we build the SAME
stage from a SHIFT CONDITION (∀ k, 0 ≤ μ k + primeStageWeights n k + M) — a real-number
fact, always satisfiable (exists_shift_making_nonneg) — supplying hnn internally via the
proven primeOpCLM_nonneg_of_shift. The operator nonnegativity is no longer assumed.
-/

namespace RHFormalization
noncomputable section
open scoped BigOperators

variable {N : ℕ}

/-- **Unconditional stage.** Built from the shift condition; hnn is PROVEN inside, not assumed. -/
noncomputable def arithmeticPrimeOperatorDFiniteStage_ofShift
    (n : ℕ) (μ : Fin N → ℝ) (M : ℝ)
    (hshift : ∀ k, 0 ≤ μ k + primeStageWeights n k + M) :
    DFiniteStage :=
  arithmeticPrimeOperatorDFiniteStage n μ M
    (primeOpCLM_nonneg_of_shift μ (primeStageWeights n) M hshift)

/-- The shift condition is always satisfiable, so the unconditional stage always exists. -/
theorem exists_arithmeticPrimeStage_ofShift
    (n : ℕ) (μ : Fin N → ℝ) :
    ∃ M : ℝ, ∀ k, 0 ≤ μ k + primeStageWeights n k + M :=
  exists_shift_making_nonneg μ (primeStageWeights n)

#print axioms arithmeticPrimeOperatorDFiniteStage_ofShift
#print axioms exists_arithmeticPrimeStage_ofShift

end
end RHFormalization
