import RHFormalization.RealPrimeShiftedLaplaceMajorantFields
import RHFormalization.CanonicalPrimePowerRCutoffExhaustion
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/--
Index exhaustion for the real-prime aligned layer, reduced to the standard
R-cutoff containment facts.

This discharges the `h_indices_eventually_contains` field once we provide:
  1. alpha n has R → ∞;
  2. every valid q with q.center ≤ alpha n.R is in the finite index set.
-/
theorem realPrimeShiftedLaplace_indices_eventually_contains_of_R_cutoff
    (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (h_R_tendsto_atTop :
      Tendsto
        (fun n : ℕ => (alpha n).R)
        Filter.atTop
        Filter.atTop)
    (h_indices_contains_of_center_le_R :
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        IsPrimePowerPair q →
        q.center ≤ (alpha n).R →
          q ∈ (primePerturbedOperatorLayerAligned μ).toFiniteCanonicalPrimePowerFormula.indices (alpha n)) :
    ∀ q : PrimePowerPair,
      IsPrimePowerPair q →
      ∃ N0 : ℕ,
        ∀ n : ℕ,
          N0 ≤ n →
            q ∈ (primePerturbedOperatorLayerAligned μ).toFiniteCanonicalPrimePowerFormula.indices (alpha n) := by
  exact
    primePower_indices_eventually_contains_of_R_cutoff
      (primePerturbedOperatorLayerAligned μ)
      alpha
      h_R_tendsto_atTop
      h_indices_contains_of_center_le_R

#print axioms realPrimeShiftedLaplace_indices_eventually_contains_of_R_cutoff

end
end RHFormalization
