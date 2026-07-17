import RHFormalization.CanonicalPrimePowerDWindowExactSpeed

/-!
# RHFormalization.CanonicalPrimePowerDWindowExactMassExactSpeed

Exact-mass / exact-speed version of the D-window estimate package.

This file is not an RH endpoint.

The previous frontier still carried a `massBudget` field with

  enumeratedMass R_n ≤ massBudget n.

This file removes that abstraction by taking the mass budget to be exactly

  enumeratedPrimePowerMass massEnum R_n.

The remaining mass/speed requirement becomes the direct analytic estimate

  enumeratedPrimePowerMass massEnum R_n / speed s n → 0.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Exact-mass / exact-speed D-window package.

Compared with `CanonicalPrimePowerDWindowExactSpeedMassBudgetData`, this removes:

* `massBudget`;
* `h_massBudget_nonneg`;
* `h_enumeratedMass_le_massBudget`.

It replaces them with the direct exact mass/speed convergence estimate.
-/
structure CanonicalPrimePowerDWindowExactMassExactSpeedData
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

  /-- Concrete finite enumeration of prime-power pairs below cutoff. -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /--
  Compact-coordinate inverse-speed D-window estimate.
  -/
  speedRate :
    PrimePowerDWindowCompactSpeedRateData X W alpha Kshared

  /--
  Exact enumerated mass divided by D-window speed tends to zero.
  -/
  h_exactMass_div_speed_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          enumeratedPrimePowerMass massEnum ((alpha n).R) /
            speedRate.speed s n)
        Filter.atTop
        (𝓝 0)

/--
Convert exact-mass/exact-speed data into the previous exact-speed mass-budget
package by choosing

  `massBudget n := enumeratedPrimePowerMass massEnum ((alpha n).R)`.
-/
def CanonicalPrimePowerDWindowExactMassExactSpeedData.toExactSpeedMassBudgetData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactMassExactSpeedData X) :
    CanonicalPrimePowerDWindowExactSpeedMassBudgetData X :=
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

    massBudget := fun n : ℕ =>
      enumeratedPrimePowerMass S.massEnum ((S.alpha n).R)

    h_massBudget_nonneg := by
      intro n
      exact enumeratedPrimePowerMass_nonneg S.massEnum ((S.alpha n).R)

    h_enumeratedMass_le_massBudget := by
      intro n
      exact le_rfl

    speedRate := S.speedRate

    h_massBudget_div_speed_tendsto_zero := by
      intro s hs
      exact S.h_exactMass_div_speed_tendsto_zero s hs }

/--
Build `CanonicalPrimePowerExhaustionData` from exact-mass/exact-speed data.
-/
def CanonicalPrimePowerDWindowExactMassExactSpeedData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactMassExactSpeedData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toExactSpeedMassBudgetData.toExhaustionData

/--
Build `DBcanLimitData` directly from exact-mass/exact-speed data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassExactSpeed
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactMassExactSpeedData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactSpeed
    X
    S.toExactSpeedMassBudgetData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once exact-mass/exact-speed data is supplied.
-/
theorem canonicalPrimePowerDWindowExactMassExactSpeed_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactMassExactSpeedData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassExactSpeed X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowExactSpeed_h_Bcan_matches_tsum
      X
      S.toExactSpeedMassBudgetData
      s
      hs

end

end RHFormalization
