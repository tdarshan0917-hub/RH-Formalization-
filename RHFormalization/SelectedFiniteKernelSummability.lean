import RHFormalization.SelectedFiniteIndexExhaustion
import RHFormalization.SelectedFiniteCanonicalLimit
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityClosure
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget
import RHFormalization.CanonicalPrimePowerSharpCutoffDisplacementKernel
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Selected kernel summability.

This closes the `hsummable` input required by:

  buildSelectedFiniteCanonicalLimit

for the selected heat-kernel displacement kernel:
  selectedFiniteKernel α = displacementCanonicalKernel (heatKernelG 1)
-/
theorem selectedFiniteKernel_hsummable :
    ∀ s : ℂ,
      s ∈ RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0 →
      Summable
        (fun q : PrimePowerPair =>
          q.weightC *
            (selectedFiniteKernel (primePowerStage 0)) q.center s) := by
  intro s hs
  change
    Summable
      (fun q : PrimePowerPair =>
        q.weightC *
          displacementCanonicalKernel (heatKernelG (1 : ℝ)) q.center s)
  refine
    Summable.of_norm_bounded
      (heatKernelWeightedEnvelope_summable (1 : ℝ) (by norm_num))
      ?_
  intro q
  calc
    ‖q.weightC *
        displacementCanonicalKernel (heatKernelG (1 : ℝ)) q.center s‖
        =
          ‖q.weightC‖ *
            ‖displacementCanonicalKernel (heatKernelG (1 : ℝ)) q.center s‖ := by
            rw [norm_mul]
    _ ≤
          ‖q.weightC‖ *
            displacementKernelMajorant (heatKernelG (1 : ℝ)) q := by
            exact
              mul_le_mul_of_nonneg_left
                (displacementKernel_sharedKernel_norm_le_majorant
                  (heatKernelG (1 : ℝ))
                  selectedFiniteOperatorLayer.toStagePackage.sigma0
                  s
                  hs
                  q)
                (norm_nonneg q.weightC)
    _ =
          heatKernelWeightedEnvelope (1 : ℝ) q := by
            simp [heatKernelWeightedEnvelope, displacementWeightedEnvelope,
              displacementKernelMajorant]

#print axioms selectedFiniteKernel_hsummable

end
end RHFormalization
