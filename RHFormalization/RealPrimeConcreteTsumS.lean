import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.ShiftedLaplacePrimeSummable
import RHFormalization.ShiftedLaplaceSqrtReLowerBound
import RHFormalization.ShiftedLaplaceMajorant
import RHFormalization.CanonicalPrimePowerConcreteTsumPackage
import RHFormalization.CanonicalPrimePowerRCutoffExhaustion
import RHFormalization.CanonicalPrimePowerSupportAwareExhaustion
import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.DesignedRCutoffS
import Mathlib

set_option autoImplicit false

/-!
# Concrete-tsum S for the REAL prime layer (shifted-Laplace kernel).

Builds CanonicalPrimePowerConcreteTsumKernelSeriesData for
primePerturbedOperatorLayerAligned with Kshared = shiftedLaplaceHeatKernelC.

Hard analytic field h_summable = banked aligned_h_summable (von Mangoldt
Dirichlet summability + region bridge). All other fields are rfl / banked
index facts / the support-aware exhaustion helper. NO displacement kernelID,
NO s-free boundary majorant.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

/-- The shifted-Laplace prime sum converges absolutely on RightHalfPlane 1. -/
theorem aligned_h_summable
    (s : Complex)
    (hs : s ∈ RightHalfPlane (1 : Real)) :
    Summable (fun q : PrimePowerPair =>
      q.weightC * shiftedLaplaceHeatKernelC q.center s) := by
  have hregion : s ∈ shiftedLaplaceAbsConvRegion :=
    rightHalfPlane_one_subset_shiftedLaplaceAbsConvRegion hs
  have hsqrt : (1 : Real) / 2 < (Complex.sqrt (s + (1/4 : Complex))).re := hregion
  exact laplace_prime_summable_full hsqrt

variable {N : Nat}

/-- Layer-independent: the aligned layer's formula indices at a prime-power
stage are exactly the concrete below-cutoff enumeration (same reduction as the
designed layer, since both unfold .indices to diagonalSpikeActiveIndices.image). -/
theorem aligned_indices_primePowerStage (mu : Fin N -> Real) (n : Nat) :
    (primePerturbedOperatorLayerAligned mu).toFiniteCanonicalPrimePowerFormula.indices
        (primePowerStage n) =
      concretePrimePowerBelowCutoff ((n : Real) + 1) := by
  show ((primePowerStage n).diagonalSpikeActiveIndices).image
        ((primePowerStage n).diagonalSpikeToPP) =
      concretePrimePowerBelowCutoff ((n : Real) + 1)
  exact designed_indices_primePowerStage n

/-- The concrete-tsum S for the real prime layer. -/
noncomputable def realPrimeConcreteTsumS (mu : Fin N -> Real) :
    CanonicalPrimePowerConcreteTsumKernelSeriesData
      (primePerturbedOperatorLayerAligned mu) :=
  { alpha := primePowerStage
    Kshared := shiftedLaplaceHeatKernelC
    h_indices_eventually_contains := by
      apply primePower_indices_eventually_contains_of_R_cutoff
        (primePerturbedOperatorLayerAligned mu)
        primePowerStage
        primePowerStage_R_tendsto_atTop
      intro n q hq hle
      rw [aligned_indices_primePowerStage mu n]
      exact concretePrimePowerEnum.h_mem_belowCutoff ((n : Real) + 1) q hq
        (by simpa [primePowerStage] using hle)
    h_kernel_agrees_on_indices := by
      intro n q hq s
      rfl
    h_summable := by
      intro s hs
      exact aligned_h_summable s hs
    h_weighted_partial_tendsto := by
      intro s hs
      have hf_zero :
          ∀ q : PrimePowerPair, ¬ IsPrimePowerPair q ->
            q.weightC * shiftedLaplaceHeatKernelC q.center s = 0 := by
        intro q hq
        have hw : q.weightC = 0 := by
          simp [PrimePowerPair.weightC, PrimePowerPair.weightReal, hq]
        simp [hw]
      have hsum := aligned_h_summable s hs
      have hpartial :=
        finite_sum_tendsto_of_hasSum_valid_exhaustion
          (fun n : Nat =>
            (primePerturbedOperatorLayerAligned mu).toFiniteCanonicalPrimePowerFormula.indices
              (primePowerStage n))
          (fun q : PrimePowerPair => q.weightC * shiftedLaplaceHeatKernelC q.center s)
          hf_zero
          (fun q hq =>
            (primePower_indices_eventually_contains_of_R_cutoff
              (primePerturbedOperatorLayerAligned mu)
              primePowerStage
              primePowerStage_R_tendsto_atTop
              (by
                intro n q hq hle
                rw [aligned_indices_primePowerStage mu n]
                exact concretePrimePowerEnum.h_mem_belowCutoff ((n : Real) + 1) q hq
                  (by simpa [primePowerStage] using hle))) q hq)
          hsum.hasSum
      simpa [canonicalPrimePowerPackageFromKernelTsum] using hpartial }

#print axioms realPrimeConcreteTsumS

/-- The DBcan for the real prime layer, via the concrete-tsum route. -/
noncomputable def realPrimeDBcan (mu : Fin N -> Real) :
    DBcanLimitData (primePerturbedOperatorLayerAligned mu).toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerConcreteTsumKernelSeries
    (primePerturbedOperatorLayerAligned mu)
    (realPrimeConcreteTsumS mu)

#print axioms realPrimeDBcan

end

end RHFormalization
