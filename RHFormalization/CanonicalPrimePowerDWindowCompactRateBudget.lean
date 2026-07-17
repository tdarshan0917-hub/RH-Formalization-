import RHFormalization.CanonicalPrimePowerDWindowCompactRate

/-!
# RHFormalization.CanonicalPrimePowerDWindowCompactRateBudget

Rate-budget version of the compact-coordinate D-window/mass-growth package.

This file is not an RH endpoint.

The previous frontier still carried the raw convergence field

  h_massGrowth_window_tendsto_zero :
    massGrowth n * windowError s n → 0.

This file replaces that with an explicit scalar rate-budget estimate:

  massGrowth n * windowError s n ≤ rateBudget s n,
  rateBudget s n → 0.

This is a real estimate cut: the remaining work becomes proving a concrete
finite-mass/window-error product bound.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If `massGrowth n * windowError n` is nonnegative, bounded by a nonnegative
`rateBudget n`, and `rateBudget n → 0`, then the product tends to zero.
-/
theorem massGrowth_window_tendsto_zero_of_rateBudget
    (massGrowth windowError rateBudget : ℕ → ℝ)
    (h_massGrowth_nonneg :
      ∀ n : ℕ, 0 ≤ massGrowth n)
    (h_windowError_nonneg :
      ∀ n : ℕ, 0 ≤ windowError n)
    (h_rateBudget_nonneg :
      ∀ n : ℕ, 0 ≤ rateBudget n)
    (h_massGrowth_window_le_budget :
      ∀ n : ℕ,
        massGrowth n * windowError n ≤ rateBudget n)
    (h_rateBudget_tendsto_zero :
      Tendsto rateBudget Filter.atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ => massGrowth n * windowError n)
      Filter.atTop
      (𝓝 0) := by
  exact
    real_tendsto_zero_of_nonneg_bound
      (u := fun n : ℕ => massGrowth n * windowError n)
      (b := rateBudget)
      (by
        intro n
        exact
          mul_nonneg
            (h_massGrowth_nonneg n)
            (h_windowError_nonneg n))
      h_massGrowth_window_le_budget
      h_rateBudget_nonneg
      h_rateBudget_tendsto_zero

/--
Compact-coordinate D-window data with an explicit rate budget.

Compared with `CanonicalPrimePowerDWindowCompactRateMassGrowthData`, this removes

  `h_massGrowth_window_tendsto_zero`

and replaces it by:

* `rateBudget`;
* nonnegativity of `rateBudget`;
* convergence of `rateBudget` to zero;
* a pointwise product bound by `rateBudget`.
-/
structure CanonicalPrimePowerDWindowCompactRateBudgetData
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
      IsPrimePowerPair q →
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

  /-- Scalar window error used by the D-window rate estimate. -/
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

  /--
  Explicit scalar rate budget for the product
  `massGrowth n * windowError s n`.
  -/
  rateBudget : ℂ → ℕ → ℝ

  /-- Nonnegativity of the rate budget. -/
  h_rateBudget_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ rateBudget s n

  /-- The rate budget tends to zero on the D overlap half-plane. -/
  h_rateBudget_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (rateBudget s)
        Filter.atTop
        (𝓝 0)

  /--
  Product estimate: mass growth times window error is bounded by the rate budget.
  -/
  h_massGrowth_window_le_budget :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        massGrowth n * windowError s n ≤ rateBudget s n

  /--
  Compact-coordinate D-window rate package.
  -/
  compactRate :
    PrimePowerDWindowCompactRateData X W alpha Kshared windowError

/--
Convert the rate-budget package into the previous compact-rate/mass-growth
package by proving `h_massGrowth_window_tendsto_zero`.
-/
def CanonicalPrimePowerDWindowCompactRateBudgetData.toCompactRateMassGrowthData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowCompactRateBudgetData X) :
    CanonicalPrimePowerDWindowCompactRateMassGrowthData X :=
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
    massGrowth := S.massGrowth
    h_massGrowth_nonneg := S.h_massGrowth_nonneg
    h_enumeratedMass_le_growth := S.h_enumeratedMass_le_growth

    h_massGrowth_window_tendsto_zero := by
      intro s hs
      exact
        massGrowth_window_tendsto_zero_of_rateBudget
          S.massGrowth
          (S.windowError s)
          (S.rateBudget s)
          S.h_massGrowth_nonneg
          (S.h_windowError_nonneg s hs)
          (S.h_rateBudget_nonneg s hs)
          (S.h_massGrowth_window_le_budget s hs)
          (S.h_rateBudget_tendsto_zero s hs)

    compactRate := S.compactRate }

/--
Build `CanonicalPrimePowerExhaustionData` from compact-rate budget data.
-/
def CanonicalPrimePowerDWindowCompactRateBudgetData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowCompactRateBudgetData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toCompactRateMassGrowthData.toExhaustionData

/--
Build `DBcanLimitData` directly from compact-rate budget data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowCompactRateBudget
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowCompactRateBudgetData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowCompactRateMassGrowth
    X
    S.toCompactRateMassGrowthData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once compact-rate budget data is supplied.
-/
theorem canonicalPrimePowerDWindowCompactRateBudget_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowCompactRateBudgetData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowCompactRateBudget X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowCompactRateMassGrowth_h_Bcan_matches_tsum
      X
      S.toCompactRateMassGrowthData
      s
      hs

end

end RHFormalization
