import RHFormalization.CanonicalPrimePowerSummabilityMajorant
import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.ShiftedLaplaceDSharedBridge
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

variable {N : ℕ}

/--
B-side DBcan for the REAL prime layer, built through the concrete-tsum/majorant route.

This is the route that avoids the displacement kernelID / mass-envelope path.
The remaining work is to construct the input majorant data with
Kshared := shiftedLaplaceHeatKernelC.
-/
def realPrimeShiftedLaplaceDBcan_fromMajorant
    (μ : Fin N → ℝ)
    (S : CanonicalPrimePowerMajorantKernelSeriesData
          (primePerturbedOperatorLayerAligned μ)) :
    DBcanLimitData (primePerturbedOperatorLayerAligned μ).toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerMajorantKernelSeries
    (primePerturbedOperatorLayerAligned μ)
    S

/--
The resulting Bcan is the concrete shifted prime-power tsum, provided S.Kshared is
the shifted-Laplace kernel.
-/
theorem realPrimeShiftedLaplaceDBcan_fromMajorant_matches_tsum
    (μ : Fin N → ℝ)
    (S : CanonicalPrimePowerMajorantKernelSeriesData
          (primePerturbedOperatorLayerAligned μ))
    (s : ℂ)
    (hs : s ∈ RightHalfPlane (primePerturbedOperatorLayerAligned μ).toStagePackage.sigma0) :
    (realPrimeShiftedLaplaceDBcan_fromMajorant μ S).Bcan s =
      ∑' q : PrimePowerPair, q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerMajorantKernelSeries_h_Bcan_matches_tsum
      (primePerturbedOperatorLayerAligned μ)
      S
      s
      hs

#print axioms realPrimeShiftedLaplaceDBcan_fromMajorant
#print axioms realPrimeShiftedLaplaceDBcan_fromMajorant_matches_tsum

end
end RHFormalization
