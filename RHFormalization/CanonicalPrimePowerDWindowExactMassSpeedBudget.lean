import RHFormalization.CanonicalPrimePowerDWindowSpeedBudget

/-!
# RHFormalization.CanonicalPrimePowerDWindowExactMassSpeedBudget

Exact enumerated-mass version of the D-window speed-budget package.

This file is not an RH endpoint.

The previous frontier still carried an abstract `massGrowth` field together with

  h_enumeratedMass_le_growth :
    enumeratedMass R_n ≤ massGrowth n.

This file removes that abstraction by setting

  massGrowth n := ∑ q in belowCutoff R_n, ‖q.weightC‖.

Then the remaining mass estimate is the direct bound

  enumeratedMass R_n ≤ massBudget n.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The exact enumerated prime-power mass below cutoff `R`.
-/
noncomputable def enumeratedPrimePowerMass
    (massEnum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ) : ℝ :=
  (massEnum.belowCutoff R).sum
    (fun q : PrimePowerPair => ‖q.weightC‖)

/--
The exact enumerated prime-power mass is nonnegative.
-/
theorem enumeratedPrimePowerMass_nonneg
    (massEnum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ) :
    0 ≤ enumeratedPrimePowerMass massEnum R := by
  dsimp [enumeratedPrimePowerMass]
  exact
    Finset.sum_nonneg
      (fun q hq => norm_nonneg q.weightC)

/--
Speed-budget data where the mass growth is exactly the enumerated cutoff mass.

Compared with `CanonicalPrimePowerDWindowSpeedBudgetData`, this removes:

* `massGrowth`;
* `h_massGrowth_nonneg`;
* `h_enumeratedMass_le_growth`;
* `h_massGrowth_le_massBudget`.

It replaces them by the direct estimate:

  exact enumerated mass ≤ massBudget.
-/
structure CanonicalPrimePowerDWindowExactMassSpeedBudgetData
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

  /-- Separate upper bound for the exact enumerated prime-power mass. -/
  massBudget : ℕ → ℝ

  /-- Nonnegativity of the mass budget. -/
  h_massBudget_nonneg :
    ∀ n : ℕ, 0 ≤ massBudget n

  /--
  Direct mass estimate:

    exact enumerated mass below `R_n` is bounded by `massBudget n`.
  -/
  h_enumeratedMass_le_massBudget :
    ∀ n : ℕ,
      enumeratedPrimePowerMass massEnum ((alpha n).R) ≤
        massBudget n

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

  /-- D-window speed. Larger speed means faster D-window decay. -/
  speed : ℂ → ℕ → ℝ

  /-- Positivity of the speed. -/
  h_speed_pos :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 < speed s n

  /-- Window budget is bounded by inverse speed. -/
  h_windowBudget_le_inv_speed :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        windowBudget s n ≤ (1 : ℝ) / speed s n

  /--
  Exact enumerated mass budget divided by D-window speed tends to zero.
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
Convert exact enumerated-mass speed-budget data into the previous speed-budget
package.
-/
def CanonicalPrimePowerDWindowExactMassSpeedBudgetData.toSpeedBudgetData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactMassSpeedBudgetData X) :
    CanonicalPrimePowerDWindowSpeedBudgetData X :=
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

    massGrowth := fun n : ℕ =>
      enumeratedPrimePowerMass S.massEnum ((S.alpha n).R)

    h_massGrowth_nonneg := by
      intro n
      exact enumeratedPrimePowerMass_nonneg S.massEnum ((S.alpha n).R)

    h_enumeratedMass_le_growth := by
      intro n
      simpa [enumeratedPrimePowerMass] using
        (le_rfl :
          (S.massEnum.belowCutoff ((S.alpha n).R)).sum
              (fun q : PrimePowerPair => ‖q.weightC‖)
            ≤
          (S.massEnum.belowCutoff ((S.alpha n).R)).sum
              (fun q : PrimePowerPair => ‖q.weightC‖))

    massBudget := S.massBudget
    h_massBudget_nonneg := S.h_massBudget_nonneg

    h_massGrowth_le_massBudget := by
      intro n
      exact S.h_enumeratedMass_le_massBudget n

    windowBudget := S.windowBudget
    h_windowBudget_nonneg := S.h_windowBudget_nonneg
    h_windowError_le_windowBudget := S.h_windowError_le_windowBudget

    speed := S.speed
    h_speed_pos := S.h_speed_pos
    h_windowBudget_le_inv_speed := S.h_windowBudget_le_inv_speed
    h_massBudget_div_speed_tendsto_zero :=
      S.h_massBudget_div_speed_tendsto_zero

    compactRate := S.compactRate }

/--
Build `CanonicalPrimePowerExhaustionData` from exact-mass speed-budget data.
-/
def CanonicalPrimePowerDWindowExactMassSpeedBudgetData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactMassSpeedBudgetData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toSpeedBudgetData.toExhaustionData

/--
Build `DBcanLimitData` directly from exact-mass speed-budget data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassSpeedBudget
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactMassSpeedBudgetData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowSpeedBudget
    X
    S.toSpeedBudgetData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once exact-mass speed-budget data is supplied.
-/
theorem canonicalPrimePowerDWindowExactMassSpeedBudget_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactMassSpeedBudgetData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassSpeedBudget X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowSpeedBudget_h_Bcan_matches_tsum
      X
      S.toSpeedBudgetData
      s
      hs

end

end RHFormalization
