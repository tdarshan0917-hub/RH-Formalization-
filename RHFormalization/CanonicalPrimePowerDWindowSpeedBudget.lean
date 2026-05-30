import RHFormalization.CanonicalPrimePowerDWindowSeparatedRateBudget

/-!
# RHFormalization.CanonicalPrimePowerDWindowSpeedBudget

Speed-budget version of the compact-coordinate D-window/mass estimate.

This file is not an RH endpoint.

The previous layer reduced the product estimate to

  massBudget n * windowBudget s n → 0.

This file replaces that raw product-convergence field by the more analytic
rate comparison:

  windowBudget s n ≤ 1 / speed s n,
  massBudget n / speed s n → 0.

This expresses the real Appendix-D requirement: the D-window convergence speed
dominates the finite prime-power mass growth.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the window budget is bounded by `1 / speed n`, and the mass budget divided by
that speed tends to zero, then the mass/window product tends to zero.
-/
theorem massWindowBudget_tendsto_zero_of_speed
    (massBudget windowBudget speed : ℕ → ℝ)
    (h_massBudget_nonneg :
      ∀ n : ℕ, 0 ≤ massBudget n)
    (h_windowBudget_nonneg :
      ∀ n : ℕ, 0 ≤ windowBudget n)
    (h_speed_pos :
      ∀ n : ℕ, 0 < speed n)
    (h_windowBudget_le_inv_speed :
      ∀ n : ℕ, windowBudget n ≤ (1 : ℝ) / speed n)
    (h_massBudget_div_speed_tendsto_zero :
      Tendsto
        (fun n : ℕ => massBudget n / speed n)
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ => massBudget n * windowBudget n)
      Filter.atTop
      (𝓝 0) := by
  exact
    real_tendsto_zero_of_nonneg_bound
      (u := fun n : ℕ => massBudget n * windowBudget n)
      (b := fun n : ℕ => massBudget n / speed n)
      (by
        intro n
        exact
          mul_nonneg
            (h_massBudget_nonneg n)
            (h_windowBudget_nonneg n))
      (by
        intro n
        have hmul :
            massBudget n * windowBudget n ≤
              massBudget n * ((1 : ℝ) / speed n) :=
          mul_le_mul_of_nonneg_left
            (h_windowBudget_le_inv_speed n)
            (h_massBudget_nonneg n)

        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul)
      (by
        intro n
        exact
          div_nonneg
            (h_massBudget_nonneg n)
            (le_of_lt (h_speed_pos n)))
      h_massBudget_div_speed_tendsto_zero

/--
Separated-budget data with an explicit D-window speed.

Compared with `CanonicalPrimePowerDWindowSeparatedRateBudgetData`, this removes

  `h_massWindowBudget_tendsto_zero`

and replaces it by:

* a positive speed function;
* a bound `windowBudget ≤ 1 / speed`;
* a rate comparison `massBudget / speed → 0`.
-/
structure CanonicalPrimePowerDWindowSpeedBudgetData
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

  /-- Separate upper bound for the finite prime-power mass growth. -/
  massBudget : ℕ → ℝ

  /-- Nonnegativity of the mass budget. -/
  h_massBudget_nonneg :
    ∀ n : ℕ, 0 ≤ massBudget n

  /-- Mass growth is bounded by the mass budget. -/
  h_massGrowth_le_massBudget :
    ∀ n : ℕ, massGrowth n ≤ massBudget n

  /-- Separate upper bound for the D-window error. -/
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
  D-window speed. Larger speed means faster D-window decay.
  -/
  speed : ℂ → ℕ → ℝ

  /-- Positivity of the speed. -/
  h_speed_pos :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 < speed s n

  /--
  Window budget is bounded by inverse speed.
  -/
  h_windowBudget_le_inv_speed :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        windowBudget s n ≤ (1 : ℝ) / speed s n

  /--
  Mass growth divided by D-window speed tends to zero.
  -/
  h_massBudget_div_speed_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => massBudget n / speed s n)
        Filter.atTop
        (𝓝 0)

  /--
  Compact-coordinate D-window rate package.
  -/
  compactRate :
    PrimePowerDWindowCompactRateData X W alpha Kshared windowError

/--
Convert speed-budget data into separated-budget data.
-/
def CanonicalPrimePowerDWindowSpeedBudgetData.toSeparatedRateBudgetData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSpeedBudgetData X) :
    CanonicalPrimePowerDWindowSeparatedRateBudgetData X :=
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

    massBudget := S.massBudget
    h_massBudget_nonneg := S.h_massBudget_nonneg
    h_massGrowth_le_massBudget := S.h_massGrowth_le_massBudget

    windowBudget := S.windowBudget
    h_windowBudget_nonneg := S.h_windowBudget_nonneg
    h_windowError_le_windowBudget := S.h_windowError_le_windowBudget

    h_massWindowBudget_tendsto_zero := by
      intro s hs
      exact
        massWindowBudget_tendsto_zero_of_speed
          S.massBudget
          (S.windowBudget s)
          (S.speed s)
          S.h_massBudget_nonneg
          (S.h_windowBudget_nonneg s hs)
          (S.h_speed_pos s hs)
          (S.h_windowBudget_le_inv_speed s hs)
          (S.h_massBudget_div_speed_tendsto_zero s hs)

    compactRate := S.compactRate }

/--
Build `CanonicalPrimePowerExhaustionData` from speed-budget compact-rate data.
-/
def CanonicalPrimePowerDWindowSpeedBudgetData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSpeedBudgetData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toSeparatedRateBudgetData.toExhaustionData

/--
Build `DBcanLimitData` directly from speed-budget compact-rate data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowSpeedBudget
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSpeedBudgetData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowSeparatedRateBudget
    X
    S.toSeparatedRateBudgetData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once speed-budget compact-rate data is supplied.
-/
theorem canonicalPrimePowerDWindowSpeedBudget_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSpeedBudgetData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowSpeedBudget X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowSeparatedRateBudget_h_Bcan_matches_tsum
      X
      S.toSeparatedRateBudgetData
      s
      hs

end

end RHFormalization
