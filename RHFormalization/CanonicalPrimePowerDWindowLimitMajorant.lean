import RHFormalization.CanonicalPrimePowerDWindowExactMassSpeedEstimate

/-!
# RHFormalization.CanonicalPrimePowerDWindowLimitMajorant

Shared-kernel majorant from the D-window limit kernel.

This file is not an RH endpoint.

The current sharp frontier still carries

  h_sharedKernel_norm_le_majorant :
    ‖Kshared q.center s‖ ≤ kernelMajorant q.

But the structural kernel-identification package already says

  Kshared q.center s = W.G_limit (coord s q).

So this file reduces the shared-kernel majorant to the actual D-window limit
kernel estimate

  ‖W.G_limit (coord s q)‖ ≤ kernelMajorant q.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the shared kernel is identified with the D-window limit kernel, then a
majorant for the D-window limit kernel gives the shared-kernel majorant.
-/
theorem sharedKernel_norm_le_majorant_of_window_limit
    {X : DFiniteStagePackageFromOperatorLayer}
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    {Kshared : CanonicalKernelC}
    (kernelID :
      PrimePowerDWindowKernelIdentificationData X W alpha Kshared)
    (kernelMajorant : PrimePowerPair → ℝ)
    (h_windowLimit_norm_le_majorant :
      ∀ s : ℂ,
      ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      ∀ q : PrimePowerPair,
        ‖W.G_limit (kernelID.coord s q)‖ ≤ kernelMajorant q) :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖Kshared q.center s‖ ≤ kernelMajorant q := by
  intro s hs q
  have hEq :
      Kshared q.center s =
        W.G_limit (kernelID.coord s q) :=
    kernelID.h_shared_kernel_eq_limit s hs q
  rw [hEq]
  exact h_windowLimit_norm_le_majorant s hs q

/--
Exact-mass/speed data where the shared-kernel majorant is derived from the
D-window limit-kernel majorant.

Compared with `CanonicalPrimePowerDWindowExactMassSpeedEstimateData`, this
removes `h_sharedKernel_norm_le_majorant` and replaces it with
`h_windowLimit_norm_le_majorant`.
-/
structure CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData
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

  /-- Unweighted majorant for the shared/D-window limit kernel. -/
  kernelMajorant : PrimePowerPair → ℝ

  /-- Nonnegativity of the unweighted kernel majorant. -/
  h_kernelMajorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ kernelMajorant q

  /--
  Compact-coordinate inverse-speed D-window estimate, including structural
  kernel-identification data.
  -/
  speedRate :
    PrimePowerDWindowCompactSpeedRateData X W alpha Kshared

  /--
  Majorant for the D-window limit kernel.
  -/
  h_windowLimit_norm_le_majorant :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖W.G_limit (speedRate.kernelID.coord s q)‖ ≤ kernelMajorant q

  /-- Summability of the weighted shared-kernel majorant. -/
  h_weightedKernelMajorant_summable :
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ * kernelMajorant q)

  /-- Concrete finite enumeration of prime-power pairs below cutoff. -/
  massEnum : PrimePowerWeightCutoffEnumerationData

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
Convert D-window limit-majorant data into the previous exact-mass/speed estimate
package.
-/
def CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData.toExactMassSpeedEstimateData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData X) :
    CanonicalPrimePowerDWindowExactMassSpeedEstimateData X :=
  { W := S.W
    alpha := S.alpha
    Kshared := S.Kshared

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R := S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := S.h_indices_subset_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg

    h_sharedKernel_norm_le_majorant :=
      sharedKernel_norm_le_majorant_of_window_limit
        S.speedRate.kernelID
        S.kernelMajorant
        S.h_windowLimit_norm_le_majorant

    h_weightedKernelMajorant_summable :=
      S.h_weightedKernelMajorant_summable

    massEnum := S.massEnum
    speedRate := S.speedRate

    massUpper := S.massUpper
    h_massUpper_nonneg := S.h_massUpper_nonneg
    h_exactMass_le_massUpper := S.h_exactMass_le_massUpper

    speedLower := S.speedLower
    h_speedLower_pos := S.h_speedLower_pos
    h_speedLower_le_speed := S.h_speedLower_le_speed

    h_massUpper_div_speedLower_tendsto_zero :=
      S.h_massUpper_div_speedLower_tendsto_zero }

/--
Build `CanonicalPrimePowerExhaustionData` from D-window limit-majorant /
mass-speed estimate data.
-/
def CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toExactMassSpeedEstimateData.toExhaustionData

/--
Build `DBcanLimitData` directly from D-window limit-majorant / mass-speed data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowLimitMajorant
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassSpeedEstimate
    X
    S.toExactMassSpeedEstimateData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once D-window limit-majorant / mass-speed data is supplied.
-/
theorem canonicalPrimePowerDWindowLimitMajorant_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowLimitMajorant X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowExactMassSpeedEstimate_h_Bcan_matches_tsum
      X
      S.toExactMassSpeedEstimateData
      s
      hs

end

end RHFormalization
