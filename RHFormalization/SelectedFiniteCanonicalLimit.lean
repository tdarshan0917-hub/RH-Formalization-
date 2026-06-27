import RHFormalization.SelectedFiniteCanonicalLimitTarget
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
Selected finite-canonical limit builder.

This is the missing L-provider layer for:

  selected_direct_final_RH_from_wrapper_layer

It reduces L to the exact three finite-canonical convergence inputs:
  1. valid prime-power index exhaustion;
  2. shared-kernel summability;
  3. finite kernel-error tends to zero.
-/

noncomputable def selectedDirectC : CanonicalPrimePowerPackage :=
  canonicalPrimePowerPackageFromKernelTsum
    selectedFiniteOperatorLayer.toStagePackage.sigma0
    (selectedFiniteKernel (primePowerStage 0))

noncomputable def buildSelectedFiniteCanonicalLimit
    (hmem :
      ∀ q : PrimePowerPair, IsPrimePowerPair q →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          q ∈ selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
                (primePowerStage n))
    (hsummable :
      ∀ s : ℂ,
        s ∈ RightHalfPlane selectedFiniteOperatorLayer.toStagePackage.sigma0 →
        Summable
          (fun q : PrimePowerPair =>
            q.weightC *
              (selectedFiniteKernel (primePowerStage 0)) q.center s))
    (herror :
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
          (𝓝 0)) :
    DOperatorFiniteCanonicalLimitAtOverlapData
      selectedFiniteOperatorLayer
      selectedDirectC :=
  DOperatorFiniteCanonicalLimitAtOverlapData.mk
    (fun n => primePowerStage n)
    (by rfl)
    (by
      intro s hs
      change
        Tendsto
          (fun n : ℕ =>
            finiteCanonicalPrimePowerPackage
              (selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
                (primePowerStage n))
              (selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.kernel
                (primePowerStage n))
              s)
          Filter.atTop
          (𝓝 (selectedDirectC.Bshared s))
      exact
        finiteCanonical_tendsto_tsum_of_kernel_error_tendsto_zero_valid
          (fun n =>
            selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices
              (primePowerStage n))
          (fun n =>
            selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.kernel
              (primePowerStage n))
          (selectedFiniteKernel (primePowerStage 0))
          s
          hmem
          (hsummable s hs)
          (herror s hs))

#print axioms buildSelectedFiniteCanonicalLimit

end
end RHFormalization
