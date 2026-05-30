import RHFormalization.FinalRHFromDWindowExactMassExactSpeed

/-!
# RHFormalization.CanonicalPrimePowerDWindowExactMassSpeedEstimate

Mass-upper / speed-lower estimate layer for exact-mass/exact-speed data.

This file is not an RH endpoint.

The current sharp frontier contains the analytic field

  enumeratedPrimePowerMass massEnum R_n / speed s n → 0.

This file reduces it to three more concrete estimates:

* exact enumerated prime-power mass is bounded by `massUpper n`;
* the D-window speed is bounded below by `speedLower s n`;
* `massUpper n / speedLower s n → 0`.

This is a direct attack on the exact mass/speed convergence field.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If exact mass is bounded above by `massUpper`, and speed is bounded below by
`speedLower`, then `exactMass / speed → 0` follows from
`massUpper / speedLower → 0`.
-/
theorem exactMass_div_speed_tendsto_zero_of_upper_lower
    (exactMass massUpper speed speedLower : ℕ → ℝ)
    (h_exactMass_nonneg :
      ∀ n : ℕ, 0 ≤ exactMass n)
    (h_massUpper_nonneg :
      ∀ n : ℕ, 0 ≤ massUpper n)
    (h_speed_pos :
      ∀ n : ℕ, 0 < speed n)
    (h_speedLower_pos :
      ∀ n : ℕ, 0 < speedLower n)
    (h_exactMass_le_massUpper :
      ∀ n : ℕ, exactMass n ≤ massUpper n)
    (h_speedLower_le_speed :
      ∀ n : ℕ, speedLower n ≤ speed n)
    (h_massUpper_div_speedLower_tendsto_zero :
      Tendsto
        (fun n : ℕ => massUpper n / speedLower n)
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ => exactMass n / speed n)
      Filter.atTop
      (𝓝 0) := by
  exact
    real_tendsto_zero_of_nonneg_bound
      (u := fun n : ℕ => exactMass n / speed n)
      (b := fun n : ℕ => massUpper n / speedLower n)
      (by
        intro n
        exact
          div_nonneg
            (h_exactMass_nonneg n)
            (le_of_lt (h_speed_pos n)))
      (by
        intro n

        have hinv :
            (speed n)⁻¹ ≤ (speedLower n)⁻¹ := by
          have hdiv :
              (1 : ℝ) / speed n ≤ (1 : ℝ) / speedLower n :=
            one_div_le_one_div_of_le
              (h_speedLower_pos n)
              (h_speedLower_le_speed n)
          simpa [one_div] using hdiv

        have h1 :
            exactMass n / speed n ≤
              exactMass n / speedLower n := by
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left
              hinv
              (h_exactMass_nonneg n)

        have hinvLower_nonneg :
            0 ≤ (speedLower n)⁻¹ :=
          inv_nonneg.mpr
            (le_of_lt (h_speedLower_pos n))

        have h2 :
            exactMass n / speedLower n ≤
              massUpper n / speedLower n := by
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right
              (h_exactMass_le_massUpper n)
              hinvLower_nonneg

        exact le_trans h1 h2)
      (by
        intro n
        exact
          div_nonneg
            (h_massUpper_nonneg n)
            (le_of_lt (h_speedLower_pos n)))
      h_massUpper_div_speedLower_tendsto_zero

/--
Exact-mass/exact-speed data where the mass/speed convergence is proved from an
upper mass bound and a lower speed bound.
-/
structure CanonicalPrimePowerDWindowExactMassSpeedEstimateData
    (X : DFiniteStagePackageFromOperatorLayer) where

  /-- D-window data used to represent finite and shared kernels. -/
  W : DCanonicalWindowData

  alpha : ℕ → DFiniteStage

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /-- Concrete cutoff growth: the prime-power cutoff dominates the stage index. -/
  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

  /-- The finite stage index set contains every prime-power pair below cutoff. -/
  h_indices_contains_of_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q.center ≤ (alpha n).R →
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  /-- The finite stage index set contains only indices below cutoff. -/
  h_indices_subset_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        q.center ≤ (alpha n).R

  /-- Unweighted majorant for the shared kernel. -/
  kernelMajorant : PrimePowerPair → ℝ

  /-- Nonnegativity of the unweighted kernel majorant. -/
  h_kernelMajorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ kernelMajorant q

  /-- Pointwise unweighted shared-kernel bound on the D overlap half-plane. -/
  h_sharedKernel_norm_le_majorant :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ q : PrimePowerPair,
        ‖Kshared q.center s‖ ≤ kernelMajorant q

  /-- Summability of the weighted shared-kernel majorant. -/
  h_weightedKernelMajorant_summable :
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ * kernelMajorant q)

  /-- Concrete finite enumeration of prime-power pairs below cutoff. -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /--
  Compact-coordinate inverse-speed D-window estimate.
  -/
  speedRate :
    PrimePowerDWindowCompactSpeedRateData X W alpha Kshared

  /--
  Upper bound for exact enumerated prime-power mass.
  -/
  massUpper : ℕ → ℝ

  /-- Nonnegativity of the mass upper bound. -/
  h_massUpper_nonneg :
    ∀ n : ℕ, 0 ≤ massUpper n

  /--
  Exact enumerated mass below `R_n` is bounded by `massUpper n`.
  -/
  h_exactMass_le_massUpper :
    ∀ n : ℕ,
      enumeratedPrimePowerMass massEnum ((alpha n).R) ≤
        massUpper n

  /--
  Lower bound for the D-window speed.
  -/
  speedLower : ℂ → ℕ → ℝ

  /-- Positivity of the speed lower bound. -/
  h_speedLower_pos :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 < speedLower s n

  /--
  The speed lower bound is below the actual D-window speed.
  -/
  h_speedLower_le_speed :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        speedLower s n ≤ speedRate.speed s n

  /--
  Mass upper bound divided by speed lower bound tends to zero.
  -/
  h_massUpper_div_speedLower_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => massUpper n / speedLower s n)
        Filter.atTop
        (𝓝 0)

/--
Convert mass-upper / speed-lower estimate data into exact-mass/exact-speed data.
-/
def CanonicalPrimePowerDWindowExactMassSpeedEstimateData.toExactMassExactSpeedData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactMassSpeedEstimateData X) :
    CanonicalPrimePowerDWindowExactMassExactSpeedData X :=
  { W := S.W
    alpha := S.alpha
    Kshared := S.Kshared

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R := S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := S.h_indices_subset_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg
    h_sharedKernel_norm_le_majorant := S.h_sharedKernel_norm_le_majorant
    h_weightedKernelMajorant_summable := S.h_weightedKernelMajorant_summable

    massEnum := S.massEnum
    speedRate := S.speedRate

    h_exactMass_div_speed_tendsto_zero := by
      intro s hs
      exact
        exactMass_div_speed_tendsto_zero_of_upper_lower
          (fun n : ℕ =>
            enumeratedPrimePowerMass S.massEnum ((S.alpha n).R))
          S.massUpper
          (S.speedRate.speed s)
          (S.speedLower s)
          (fun n : ℕ =>
            enumeratedPrimePowerMass_nonneg
              S.massEnum
              ((S.alpha n).R))
          S.h_massUpper_nonneg
          (S.speedRate.h_speed_pos s hs)
          (S.h_speedLower_pos s hs)
          S.h_exactMass_le_massUpper
          (S.h_speedLower_le_speed s hs)
          (S.h_massUpper_div_speedLower_tendsto_zero s hs) }

/--
Build `CanonicalPrimePowerExhaustionData` from mass-upper/speed-lower data.
-/
def CanonicalPrimePowerDWindowExactMassSpeedEstimateData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactMassSpeedEstimateData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toExactMassExactSpeedData.toExhaustionData

/--
Build `DBcanLimitData` directly from mass-upper/speed-lower data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassSpeedEstimate
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactMassSpeedEstimateData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassExactSpeed
    X
    S.toExactMassExactSpeedData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once mass-upper/speed-lower data is supplied.
-/
theorem canonicalPrimePowerDWindowExactMassSpeedEstimate_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactMassSpeedEstimateData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassSpeedEstimate X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowExactMassExactSpeed_h_Bcan_matches_tsum
      X
      S.toExactMassExactSpeedData
      s
      hs

end

end RHFormalization
