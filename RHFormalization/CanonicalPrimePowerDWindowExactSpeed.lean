import RHFormalization.CanonicalPrimePowerDWindowExactMassSpeedBudget

/-!
# RHFormalization.CanonicalPrimePowerDWindowExactSpeed

Exact-speed version of the compact-coordinate D-window estimate.

This file is not an RH endpoint.

The previous frontier still carried abstract `windowError` and `windowBudget`
functions together with comparison fields:

  windowError ≤ windowBudget,
  windowBudget ≤ 1 / speed.

This file removes those abstractions by taking the D-window error itself to be

  1 / speed.

The remaining D.CANONICAL-WINDOW estimate is therefore the concrete compact-rate
bound

  dist (W.gbar_stage (alpha n) a) (W.G_limit a) ≤ 1 / speed s n.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Compact-coordinate D-window speed-rate data.

This is the concrete D.CANONICAL-WINDOW estimate in inverse-speed form.
-/
structure PrimePowerDWindowCompactSpeedRateData
    (X : DFiniteStagePackageFromOperatorLayer)
    (W : DCanonicalWindowData)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC) where

  /--
  Structural identification of the prime-power kernels with the D-window kernels.
  -/
  kernelID :
    PrimePowerDWindowKernelIdentificationData X W alpha Kshared

  /--
  Compact real coordinate set for each complex point `s`.
  -/
  coordSet :
    ℂ → Set ℝ

  /--
  Compactness of the coordinate set on the D overlap half-plane.
  -/
  h_coordSet_compact :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      IsCompact (coordSet s)

  /--
  Active finite-stage prime-power coordinates lie inside the compact coordinate
  set.
  -/
  h_coord_mem :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        kernelID.coord s q ∈ coordSet s

  /--
  D-window convergence speed. Larger speed means smaller window error.
  -/
  speed : ℂ → ℕ → ℝ

  /-- Positivity of the speed. -/
  h_speed_pos :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
      0 < speed s n

  /--
  Concrete compact-coordinate D.CANONICAL-WINDOW inverse-speed estimate.
  -/
  h_compact_window_speed_rate :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ a : ℝ,
      a ∈ coordSet s →
        dist
          (W.gbar_stage (alpha n) a)
          (W.G_limit a) ≤
            (1 : ℝ) / speed s n

/--
Build the previous compact-rate data from inverse-speed compact-window data.

The package-level window error is chosen to be exactly `1 / speed`.
-/
def PrimePowerDWindowCompactSpeedRateData.toCompactRateData
    {X : DFiniteStagePackageFromOperatorLayer}
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    {Kshared : CanonicalKernelC}
    (S : PrimePowerDWindowCompactSpeedRateData X W alpha Kshared) :
    PrimePowerDWindowCompactRateData
      X
      W
      alpha
      Kshared
      (fun s n => (1 : ℝ) / S.speed s n) :=
  { kernelID := S.kernelID
    coordSet := S.coordSet
    h_coordSet_compact := S.h_coordSet_compact
    h_coord_mem := S.h_coord_mem
    h_compact_window_rate := by
      intro s hs n a ha
      exact S.h_compact_window_speed_rate s hs n a ha }

/--
Exact-speed / exact-mass D-window data.

Compared with `CanonicalPrimePowerDWindowExactMassSpeedBudgetData`, this removes:

* `windowError`;
* `windowBudget`;
* `h_windowError_nonneg`;
* `h_windowError_le_windowBudget`;
* `h_windowBudget_nonneg`;
* `h_windowBudget_le_inv_speed`;

and replaces them by the single compact inverse-speed window estimate.
-/
structure CanonicalPrimePowerDWindowExactSpeedMassBudgetData
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

  /--
  Compact-coordinate inverse-speed D-window estimate.
  -/
  speedRate :
    PrimePowerDWindowCompactSpeedRateData X W alpha Kshared

  /--
  Exact enumerated mass budget divided by D-window speed tends to zero.
  -/
  h_massBudget_div_speed_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => massBudget n / speedRate.speed s n)
        Filter.atTop
        (𝓝 0)

/--
Convert exact-speed/exact-mass data into the previous exact-mass speed-budget
package.
-/
def CanonicalPrimePowerDWindowExactSpeedMassBudgetData.toExactMassSpeedBudgetData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactSpeedMassBudgetData X) :
    CanonicalPrimePowerDWindowExactMassSpeedBudgetData X :=
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

    windowError := fun s n =>
      (1 : ℝ) / S.speedRate.speed s n

    h_windowError_nonneg := by
      intro s hs n
      exact
        div_nonneg
          zero_le_one
          (le_of_lt (S.speedRate.h_speed_pos s hs n))

    massEnum := S.massEnum

    massBudget := S.massBudget
    h_massBudget_nonneg := S.h_massBudget_nonneg
    h_enumeratedMass_le_massBudget := S.h_enumeratedMass_le_massBudget

    windowBudget := fun s n =>
      (1 : ℝ) / S.speedRate.speed s n

    h_windowBudget_nonneg := by
      intro s hs n
      exact
        div_nonneg
          zero_le_one
          (le_of_lt (S.speedRate.h_speed_pos s hs n))

    h_windowError_le_windowBudget := by
      intro s hs n
      rfl

    speed := S.speedRate.speed
    h_speed_pos := S.speedRate.h_speed_pos

    h_windowBudget_le_inv_speed := by
      intro s hs n
      rfl

    h_massBudget_div_speed_tendsto_zero :=
      S.h_massBudget_div_speed_tendsto_zero

    compactRate :=
      S.speedRate.toCompactRateData }

/--
Build `CanonicalPrimePowerExhaustionData` from exact-speed/exact-mass data.
-/
def CanonicalPrimePowerDWindowExactSpeedMassBudgetData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactSpeedMassBudgetData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toExactMassSpeedBudgetData.toExhaustionData

/--
Build `DBcanLimitData` directly from exact-speed/exact-mass data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactSpeed
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactSpeedMassBudgetData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactMassSpeedBudget
    X
    S.toExactMassSpeedBudgetData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once exact-speed/exact-mass data is supplied.
-/
theorem canonicalPrimePowerDWindowExactSpeed_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactSpeedMassBudgetData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactSpeed X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowExactMassSpeedBudget_h_Bcan_matches_tsum
      X
      S.toExactMassSpeedBudgetData
      s
      hs

end

end RHFormalization
