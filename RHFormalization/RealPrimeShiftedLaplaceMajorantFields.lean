import RHFormalization.RealPrimeShiftedLaplaceDBcanFromMajorant
import RHFormalization.CanonicalPrimePowerRCutoffExhaustion
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/--
The real-prime aligned layer uses the shifted-Laplace kernel on every finite
canonical prime-power index set.

This discharges the `h_kernel_agrees_on_indices` field for the
majorant/concrete-tsum DBcan route.
-/
theorem realPrimeShiftedLaplace_kernel_agrees_on_indices
    (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage) :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ (primePerturbedOperatorLayerAligned μ).toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        ∀ s : ℂ,
          (primePerturbedOperatorLayerAligned μ).toFiniteCanonicalPrimePowerFormula.kernel
              (alpha n) q.center s =
            shiftedLaplaceHeatKernelC q.center s := by
  intro n q hq s
  dsimp [
    DFiniteStagePackageFromOperatorLayer.toFiniteCanonicalPrimePowerFormula,
    primePerturbedOperatorLayerAligned,
    primePerturbedPayloadAligned,
    buildSelectedFiniteOperatorLayerFromCanonicalPayload
  ]
  rfl

#print axioms realPrimeShiftedLaplace_kernel_agrees_on_indices

end
end RHFormalization
