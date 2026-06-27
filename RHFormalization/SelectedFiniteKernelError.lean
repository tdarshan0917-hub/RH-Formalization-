import RHFormalization.SelectedFiniteKernelSummability
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Selected kernel-error vanishes.

This closes the `herror` input required by:

  buildSelectedFiniteCanonicalLimit

because the selected finite-stage kernel is constant:
  selectedFiniteKernel α = displacementCanonicalKernel (heatKernelG 1)
-/
theorem selectedFiniteKernel_herror :
    ∀ s : ℂ,
      s ∈ RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0 →
        Tendsto
          (fun n : ℕ =>
            finiteCanonicalPrimePowerPackage
              (selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
                (primePowerStage n))
              (selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.kernel
                (primePowerStage n))
              s
            -
            (selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
                (primePowerStage n)).sum
              (fun q : PrimePowerPair =>
                q.weightC *
                  (selectedFiniteKernel (primePowerStage 0)) q.center s))
          Filter.atTop
          (𝓝 0) := by
  intro s hs
  change
    Tendsto
      (fun n : ℕ =>
        finiteCanonicalPrimePowerPackage
          (selectedFiniteIndices (primePowerStage n))
          (selectedFiniteKernel (primePowerStage n))
          s
        -
        (selectedFiniteIndices (primePowerStage n)).sum
          (fun q : PrimePowerPair =>
            q.weightC *
              (selectedFiniteKernel (primePowerStage 0)) q.center s))
      Filter.atTop
      (𝓝 0)
  simpa [finiteCanonicalPrimePowerPackage, selectedFiniteKernel] using
    tendsto_const_nhds (a := (0 : ℂ))

#print axioms selectedFiniteKernel_herror

end
end RHFormalization
