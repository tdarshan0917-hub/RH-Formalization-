import RHFormalization.CanonicalPrimePowerDWindowCompactRateBudget

/-!
# RHFormalization.CanonicalPrimePowerDWindowSeparatedRateBudget

Separated mass/window budget layer for the compact-coordinate D-window estimate.

This file is not an RH endpoint.

The previous layer used a direct scalar estimate

  massGrowth n * windowError s n ≤ rateBudget s n.

This file separates that into the two estimates that the manuscript actually
needs to prove:

* `massGrowth n ≤ massBudget n`;
* `windowError s n ≤ windowBudget s n`;

and then uses the product

  `massBudget n * windowBudget s n`

as the rate budget.

This is a real estimate cut: the remaining work becomes proving a prime-power
mass bound and a D-window decay bound separately.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If mass growth and window error are separately bounded, then their product is
bounded by the product of the bounds.
-/
theorem massGrowth_window_le_separated_budget
    (massGrowth massBudget : ℕ → ℝ)
    (windowError windowBudget : ℕ → ℝ)
    (h_massGrowth_le :
      ∀ n : ℕ, massGrowth n ≤ massBudget n)
    (h_windowError_le :
      ∀ n : ℕ, windowError n ≤ windowBudget n)
    (h_windowError_nonneg :
      ∀ n : ℕ, 0 ≤ windowError n)
    (h_massBudget_nonneg :
      ∀ n : ℕ, 0 ≤ massBudget n) :
    ∀ n : ℕ,
      massGrowth n * windowError n ≤
        massBudget n * windowBudget n := by
  intro n
  exact
    mul_le_mul
      (h_massGrowth_le n)
      (h_windowError_le n)
      (h_windowError_nonneg n)
      (h_massBudget_nonneg n)

/--
Compact-rate data with separated mass and window budgets.

Compared with `CanonicalPrimePowerDWindowCompactRateBudgetData`, this removes
the direct `rateBudget` field and replaces it with:

* `massBudget`;
* `windowBudget`;
* bounds for `massGrowth` and `windowError`;
* convergence of the product `massBudget * windowBudget`.
-/
structure CanonicalPrimePowerDWindowSeparatedRateBudgetData
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
  Separate upper bound for the finite prime-power mass growth.
  -/
  massBudget : ℕ → ℝ

  /-- Nonnegativity of the mass budget. -/
  h_massBudget_nonneg :
    ∀ n : ℕ, 0 ≤ massBudget n

  /-- Mass growth is bounded by the mass budget. -/
  h_massGrowth_le_massBudget :
    ∀ n : ℕ, massGrowth n ≤ massBudget n

  /--
  Separate upper bound for the D-window error.
  -/
  windowBudget : ℂ → ℕ → ℝ

  /-- Nonnegativity of the window budget. -/
  h_windowBudget_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ windowBudget s n

  /-- Window error is bounded by the window budget. -/
  h_windowError_le_windowBudget :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        windowError s n ≤ windowBudget s n

  /--
  Product decay of the separated budgets.
  -/
  h_massWindowBudget_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => massBudget n * windowBudget s n)
        Filter.atTop
        (𝓝 0)

  /--
  Compact-coordinate D-window rate package.
  -/
  compactRate :
    PrimePowerDWindowCompactRateData X W alpha Kshared windowError

/--
Convert separated-budget data into the direct rate-budget package.
-/
def CanonicalPrimePowerDWindowSeparatedRateBudgetData.toCompactRateBudgetData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSeparatedRateBudgetData X) :
    CanonicalPrimePowerDWindowCompactRateBudgetData X :=
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

    rateBudget := fun s n =>
      S.massBudget n * S.windowBudget s n

    h_rateBudget_nonneg := by
      intro s hs n
      exact
        mul_nonneg
          (S.h_massBudget_nonneg n)
          (S.h_windowBudget_nonneg s hs n)

    h_rateBudget_tendsto_zero := by
      intro s hs
      exact S.h_massWindowBudget_tendsto_zero s hs

    h_massGrowth_window_le_budget := by
      intro s hs n
      exact
        massGrowth_window_le_separated_budget
          S.massGrowth
          S.massBudget
          (S.windowError s)
          (S.windowBudget s)
          S.h_massGrowth_le_massBudget
          (S.h_windowError_le_windowBudget s hs)
          (S.h_windowError_nonneg s hs)
          S.h_massBudget_nonneg
          n

    compactRate := S.compactRate }

/--
Build `CanonicalPrimePowerExhaustionData` from separated-budget compact-rate data.
-/
def CanonicalPrimePowerDWindowSeparatedRateBudgetData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSeparatedRateBudgetData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toCompactRateBudgetData.toExhaustionData

/--
Build `DBcanLimitData` directly from separated-budget compact-rate data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowSeparatedRateBudget
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSeparatedRateBudgetData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowCompactRateBudget
    X
    S.toCompactRateBudgetData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once separated-budget compact-rate data is supplied.
-/
theorem canonicalPrimePowerDWindowSeparatedRateBudget_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSeparatedRateBudgetData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowSeparatedRateBudget X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowCompactRateBudget_h_Bcan_matches_tsum
      X
      S.toCompactRateBudgetData
      s
      hs

end

end RHFormalization
