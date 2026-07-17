import RHFormalization.PrimeSideTransformKernelPrototype
import RHFormalization.CanonicalPrimePowerActualKernelError
import RHFormalization.CanonicalPrimePowerAsymptoticKernel

/-!
# RHFormalization.ShiftedLaplaceDSharedBridge

This file does NOT edit or replace the existing D-side construction.

It records the precise parallel-package bridge:

If the generic D-side kernel-convergence data is supplied with

  Kshared = shiftedLaplaceHeatKernelC,

then the D-side `Bcan` produced by the generic constructor agrees on the
overlap with the shifted-Laplace prime package.

This isolates the real remaining Appendix-D-facing obligation:
provide the corresponding kernel majorant/error data for the shifted Laplace kernel.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- Shifted Laplace prime package at an arbitrary overlap threshold. -/
def shiftedLaplacePrimePackageAt (sigma0 : ℝ) : CanonicalPrimePowerPackage :=
  canonicalPrimePowerPackageFromKernelTsum sigma0 shiftedLaplaceHeatKernelC

/-- Unfolding lemma for the shifted Laplace package at threshold `sigma0`. -/
theorem shiftedLaplacePrimePackageAt_Bshared_eq_tsum
    (sigma0 : ℝ) (s : ℂ) :
    (shiftedLaplacePrimePackageAt sigma0).Bshared s =
      ∑' q : PrimePowerPair,
        q.weightC * shiftedLaplaceHeatKernelC q.center s := by
  rfl

/--
If the actual-kernel-error D data uses the shifted Laplace kernel, then the
D-side `Bcan` matches the shifted Laplace shared package on the overlap.
-/
theorem shiftedLaplace_DBcan_from_actualKernelError_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerActualKernelErrorData X)
    (hK : S.Kshared = shiftedLaplaceHeatKernelC)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerActualKernelError X S).Bcan s =
      (shiftedLaplacePrimePackageAt X.toStagePackage.sigma0).Bshared s := by
  rw [canonicalPrimePowerActualKernelError_h_Bcan_matches_tsum X S s hs]
  rw [shiftedLaplacePrimePackageAt_Bshared_eq_tsum]
  rw [hK]

/--
If the asymptotic-kernel-majorant D data uses the shifted Laplace kernel, then
the D-side `Bcan` matches the shifted Laplace shared package on the overlap.
-/
theorem shiftedLaplace_DBcan_from_asymptoticKernel_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerAsymptoticKernelMajorantData X)
    (hK : S.Kshared = shiftedLaplaceHeatKernelC)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerAsymptoticKernel X S).Bcan s =
      (shiftedLaplacePrimePackageAt X.toStagePackage.sigma0).Bshared s := by
  rw [canonicalPrimePowerAsymptoticKernel_h_Bcan_matches_tsum X S s hs]
  rw [shiftedLaplacePrimePackageAt_Bshared_eq_tsum]
  rw [hK]

#print axioms shiftedLaplacePrimePackageAt
#print axioms shiftedLaplacePrimePackageAt_Bshared_eq_tsum
#print axioms shiftedLaplace_DBcan_from_actualKernelError_matches_shared
#print axioms shiftedLaplace_DBcan_from_asymptoticKernel_matches_shared

end

end RHFormalization
