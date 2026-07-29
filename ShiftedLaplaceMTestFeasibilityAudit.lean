import RHFormalization.ShiftedLaplaceTLUFromLocalMTest
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCore
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreSummability
import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# ShiftedLaplaceMTestFeasibilityAudit

Scratch-only.

We have banked:

  ShiftedLaplaceLocalMTestData
    ⇒ shifted/Laplace hB_regular
    ⇒ shifted/Laplace h_holo, assuming hcancel + hsum + ZF.

Now we need to understand whether the local M-test data can actually be built
on all Ω for the raw shifted/Laplace prime series.

Heuristic convergence condition:

  term ~ Λ(n) n^(-1/2) exp(-log(n) * Re sqrt(s + 1/4))
       = Λ(n) n^(-(1/2 + Re sqrt(s + 1/4)))

Absolute convergence wants:

  Re sqrt(s + 1/4) > 1/2.

Ω only gives slit-plane branch control and nonzero shifted argument.
So this audit separates the absolute-convergence region from full Ω.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- Candidate absolute-convergence region for the raw shifted/Laplace prime series. -/
abbrev shiftedLaplaceAbsConvRegion : Set ℂ :=
  {s : ℂ | (1 / 2 : ℝ) < (shiftedLaplaceSqrt s).re}

/-- Candidate local-majorant shape for one open set. -/
structure ShiftedLaplaceOnePatchMTestData (U : Set ℂ) : Type 1 where
  u : PrimePowerPair → ℝ
  h_summable : Summable u
  h_bound :
    ∀ q : PrimePowerPair,
    ∀ s : ℂ,
      s ∈ U →
        ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ ≤ u q

#check ShiftedLaplaceLocalMTestData
#check shiftedLaplace_holo_from_cancellation_zeroDensity_localMTest
#check shiftedLaplace_tlu_from_local_mtest
#check shiftedLaplaceHeatKernelC
#check shiftedLaplaceHeatKernelC_apply
#check shiftedLaplaceSqrt
#check shiftedLaplaceShift
#check shiftedLaplaceShift_mem_slitPlane_of_mem_Omega
#check shiftedLaplaceShift_ne_zero_of_mem_Omega
#check finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega

#check tendstoUniformlyOn_tsum
#check TendstoUniformlyOn.tendstoLocallyUniformlyOn
#check TendstoLocallyUniformlyOn.mono
#check tendstoLocallyUniformlyOn_iUnion

-- Existing Gaussian / prime-power summability tools. These may or may not apply
-- to shifted/Laplace; this audit prints their exact names.
#check heatKernelGaussianCoreEnvelope
#check heatKernelGaussianCoreEnvelope_summable
#check heatKernelNatValueMajorant
#check heatKernelNatValueMajorant_summable
#check heatKernelGaussianCoreEnvelope_le_weight_mul_natValue_inv_cube_of_ge
#check exists_natValue_threshold_exp_neg_center_sq_le_inv_cube

/--
Sanity check: on any one patch, if a summable majorant is supplied,
the finite shifted/Laplace packages converge uniformly on that patch.
-/
theorem shiftedLaplace_tendstoUniformlyOn_of_one_patch_mtest
    (U : Set ℂ)
    (D : ShiftedLaplaceOnePatchMTestData U) :
    TendstoUniformlyOn
      (fun I : Finset PrimePowerPair =>
        finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      (fun s : ℂ =>
        ∑' q : PrimePowerPair,
          q.weightC * shiftedLaplaceHeatKernelC q.center s)
      Filter.atTop
      U := by
  simpa [finiteCanonicalPrimePowerPackage] using
    (tendstoUniformlyOn_tsum
      D.h_summable
      D.h_bound)

/--
Same patch result, converted to local-uniform convergence.
-/
theorem shiftedLaplace_tendstoLocallyUniformlyOn_of_one_patch_mtest
    (U : Set ℂ)
    (D : ShiftedLaplaceOnePatchMTestData U) :
    TendstoLocallyUniformlyOn
      (fun I : Finset PrimePowerPair =>
        finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      (fun s : ℂ =>
        ∑' q : PrimePowerPair,
          q.weightC * shiftedLaplaceHeatKernelC q.center s)
      Filter.atTop
      U :=
  (shiftedLaplace_tendstoUniformlyOn_of_one_patch_mtest U D).tendstoLocallyUniformlyOn

#print axioms shiftedLaplaceAbsConvRegion
#print axioms ShiftedLaplaceOnePatchMTestData
#print axioms shiftedLaplace_tendstoUniformlyOn_of_one_patch_mtest
#print axioms shiftedLaplace_tendstoLocallyUniformlyOn_of_one_patch_mtest

end

end RHFormalization
