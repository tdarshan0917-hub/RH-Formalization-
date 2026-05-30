import RHFormalization.CanonicalPrimePowerRCutoffRatePackaged

/-!
# RHFormalization.CanonicalPrimePowerEnumeratedMassGrowthRate

Growth-rate control for the enumerated prime-power cutoff mass.

This file is not an RH endpoint.

The current R-cutoff rate-packaged frontier contains the field

  h_enumeratedMass_window_tendsto_zero :
    (∑ q in belowCutoff R_n, ‖q.weightC‖) * windowError_n → 0.

This file reduces that field to two sharper estimates:

* enumerated cutoff mass is bounded by `massGrowth n`;
* `massGrowth n * windowError_n → 0`.

This is the next concrete mass/window-rate estimate.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the enumerated cutoff mass is bounded by `massGrowth n`, and
`massGrowth n * windowError n → 0`, then the enumerated cutoff mass times
`windowError n` tends to zero.
-/
theorem enumeratedMass_window_tendsto_zero_of_massGrowth
    (massEnum : PrimePowerWeightCutoffEnumerationData)
    (R : ℕ → ℝ)
    (windowError : ℕ → ℝ)
    (massGrowth : ℕ → ℝ)
    (h_massGrowth_nonneg :
      ∀ n : ℕ, 0 ≤ massGrowth n)
    (h_enumeratedMass_le_growth :
      ∀ n : ℕ,
        (massEnum.belowCutoff (R n)).sum
          (fun q : PrimePowerPair => ‖q.weightC‖) ≤
            massGrowth n)
    (h_windowError_nonneg :
      ∀ n : ℕ, 0 ≤ windowError n)
    (h_massGrowth_window_tendsto_zero :
      Tendsto
        (fun n : ℕ => massGrowth n * windowError n)
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (massEnum.belowCutoff (R n)).sum
          (fun q : PrimePowerPair => ‖q.weightC‖)
        * windowError n)
      Filter.atTop
      (𝓝 0) := by
  exact
    real_tendsto_zero_of_nonneg_bound
      (u := fun n : ℕ =>
        (massEnum.belowCutoff (R n)).sum
          (fun q : PrimePowerPair => ‖q.weightC‖)
        * windowError n)
      (b := fun n : ℕ => massGrowth n * windowError n)
      (by
        intro n
        exact
          mul_nonneg
            (Finset.sum_nonneg
              (fun q hq => norm_nonneg q.weightC))
            (h_windowError_nonneg n))
      (by
        intro n
        exact
          mul_le_mul_of_nonneg_right
            (h_enumeratedMass_le_growth n)
            (h_windowError_nonneg n))
      (by
        intro n
        exact
          mul_nonneg
            (h_massGrowth_nonneg n)
            (h_windowError_nonneg n))
      h_massGrowth_window_tendsto_zero

/--
Rate-packaged R-cutoff data where the enumerated mass/window convergence is not
supplied directly.

Instead, it is derived from:
* an enumerated mass growth bound;
* a growth-window product decay theorem.
-/
structure CanonicalPrimePowerRCutoffRateMassGrowthData
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

  /-- Scalar window error used by the D-window rate bridge. -/
  windowError : ℂ → ℕ → ℝ

  /-- Nonnegativity of the window error. -/
  h_windowError_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ windowError s n

  /-- Concrete finite enumeration of prime-power pairs below cutoff. -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /-- Mass-growth function bounding the enumerated cutoff mass. -/
  massGrowth : ℕ → ℝ

  /-- Nonnegativity of the mass-growth bound. -/
  h_massGrowth_nonneg :
    ∀ n : ℕ, 0 ≤ massGrowth n

  /-- Enumerated cutoff mass is bounded by `massGrowth n`. -/
  h_enumeratedMass_le_growth :
    ∀ n : ℕ,
      (massEnum.belowCutoff ((alpha n).R)).sum
        (fun q : PrimePowerPair => ‖q.weightC‖) ≤
          massGrowth n

  /-- Growth-window product tends to zero. -/
  h_massGrowth_window_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => massGrowth n * windowError s n)
        Filter.atTop
        (𝓝 0)

  /-- Pointwise D-window rate bridge at each `s` in the D overlap half-plane. -/
  rateBridge :
    ∀ s : ℂ,
      s ∈ RightHalfPlane X.toStagePackage.sigma0 →
        PrimePowerKernelWindowRateBridgeData X W alpha Kshared s

  /-- The rate bridge's local window error agrees with the package-level one. -/
  h_rateBridge_windowError :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
      (rateBridge s hs).windowError n = windowError s n

/--
Convert mass-growth-rate data into the previous rate-packaged R-cutoff data.
-/
def CanonicalPrimePowerRCutoffRateMassGrowthData.toRCutoffRatePackagedData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffRateMassGrowthData X) :
    CanonicalPrimePowerRCutoffRatePackagedData X :=
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

    windowError := S.windowError
    h_windowError_nonneg := S.h_windowError_nonneg

    massEnum := S.massEnum

    h_enumeratedMass_window_tendsto_zero := by
      intro s hs
      exact
        enumeratedMass_window_tendsto_zero_of_massGrowth
          S.massEnum
          (fun n : ℕ => (S.alpha n).R)
          (S.windowError s)
          S.massGrowth
          S.h_massGrowth_nonneg
          S.h_enumeratedMass_le_growth
          (S.h_windowError_nonneg s hs)
          (S.h_massGrowth_window_tendsto_zero s hs)

    rateBridge := S.rateBridge
    h_rateBridge_windowError := S.h_rateBridge_windowError }

/--
Build `CanonicalPrimePowerExhaustionData` from rate/mass-growth data.
-/
def CanonicalPrimePowerRCutoffRateMassGrowthData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffRateMassGrowthData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toRCutoffRatePackagedData.toExhaustionData

/--
Build `DBcanLimitData` directly from rate/mass-growth data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerRCutoffRateMassGrowth
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffRateMassGrowthData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerRCutoffRatePackaged
    X
    S.toRCutoffRatePackagedData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once rate/mass-growth data is supplied.
-/
theorem canonicalPrimePowerRCutoffRateMassGrowth_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffRateMassGrowthData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerRCutoffRateMassGrowth X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerRCutoffRatePackaged_h_Bcan_matches_tsum
      X
      S.toRCutoffRatePackagedData
      s
      hs

end

end RHFormalization
