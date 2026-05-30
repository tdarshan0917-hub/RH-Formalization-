import RHFormalization.CanonicalPrimePowerDWindowLimitMajorant

/-!
# RHFormalization.CanonicalPrimePowerDWindowSpeedAPI

D.CANONICAL-WINDOW speed API feeding the exact prime-power package.

This file is not an RH endpoint.

The current sharp frontier still carries a prime-power-specific compact window
speed estimate through

  `PrimePowerDWindowCompactSpeedRateData`.

This file reduces that to a pure D-window compact-speed theorem:

  for every compact real coordinate set `A`,
  `gbar_stage (alpha n)` converges to `G_limit` on `A`
  with inverse-speed bound.

The prime-power active-index estimate is then obtained by applying this compact
D-window theorem to the coordinate set attached to each `s`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Pure D.CANONICAL-WINDOW compact inverse-speed estimate.

This is the actual window theorem shape: it is independent of prime-power
indices except through the compact real set on which the estimate is applied.
-/
structure DCanonicalWindowCompactSpeedAPI
    (W : DCanonicalWindowData)
    (alpha : ℕ → DFiniteStage) where

  /--
  Speed attached to a compact real coordinate set.
  -/
  speed : Set ℝ → ℕ → ℝ

  /--
  Positivity of the compact-set speed.
  -/
  h_speed_pos :
    ∀ A : Set ℝ,
      IsCompact A →
        ∀ n : ℕ,
          0 < speed A n

  /--
  Compact inverse-speed D.CANONICAL-WINDOW estimate.
  -/
  h_compact_window_speed_rate :
    ∀ A : Set ℝ,
      IsCompact A →
        ∀ n : ℕ,
        ∀ a : ℝ,
          a ∈ A →
            dist
              (W.gbar_stage (alpha n) a)
              (W.G_limit a) ≤
                (1 : ℝ) / speed A n

/--
Build prime-power compact speed-rate data from the pure compact D-window speed
API and the coordinate-set bookkeeping.
-/
def buildPrimePowerDWindowCompactSpeedRateDataFromWindowSpeedAPI
    {X : DFiniteStagePackageFromOperatorLayer}
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    {Kshared : CanonicalKernelC}
    (kernelID :
      PrimePowerDWindowKernelIdentificationData X W alpha Kshared)
    (coordSet : ℂ → Set ℝ)
    (h_coordSet_compact :
      ∀ s : ℂ,
      ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
        IsCompact (coordSet s))
    (h_coord_mem :
      ∀ s : ℂ,
      ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          kernelID.coord s q ∈ coordSet s)
    (windowSpeed :
      DCanonicalWindowCompactSpeedAPI W alpha) :
    PrimePowerDWindowCompactSpeedRateData X W alpha Kshared :=
  { kernelID := kernelID
    coordSet := coordSet
    h_coordSet_compact := h_coordSet_compact
    h_coord_mem := h_coord_mem

    speed := fun s n =>
      windowSpeed.speed (coordSet s) n

    h_speed_pos := by
      intro s hs n
      exact
        windowSpeed.h_speed_pos
          (coordSet s)
          (h_coordSet_compact s hs)
          n

    h_compact_window_speed_rate := by
      intro s hs n a ha
      exact
        windowSpeed.h_compact_window_speed_rate
          (coordSet s)
          (h_coordSet_compact s hs)
          n
          a
          ha }

/--
Limit-majorant / mass-speed data where the compact window speed estimate is
supplied by the pure D.CANONICAL-WINDOW speed API.

Compared with `CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData`,
this removes the direct `speedRate` field and replaces it by:

* structural kernel identification;
* coordinate compact sets;
* coordinate membership;
* pure compact D-window speed API.
-/
structure CanonicalPrimePowerDWindowSpeedAPILimitMajorantMassSpeedData
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

  /-- Unweighted majorant for the D-window limit kernel. -/
  kernelMajorant : PrimePowerPair → ℝ

  /-- Nonnegativity of the unweighted kernel majorant. -/
  h_kernelMajorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ kernelMajorant q

  /--
  Structural identification of prime-power kernels with D-window kernels.
  -/
  kernelID :
    PrimePowerDWindowKernelIdentificationData X W alpha Kshared

  /--
  Compact real coordinate set for each `s`.
  -/
  coordSet : ℂ → Set ℝ

  /--
  Compactness of the coordinate set on the D overlap half-plane.
  -/
  h_coordSet_compact :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      IsCompact (coordSet s)

  /--
  Active finite-stage prime-power coordinates lie in the coordinate set.
  -/
  h_coord_mem :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        kernelID.coord s q ∈ coordSet s

  /--
  Pure D.CANONICAL-WINDOW compact inverse-speed theorem.
  -/
  windowSpeed :
    DCanonicalWindowCompactSpeedAPI W alpha

  /--
  Majorant for the D-window limit kernel.
  -/
  h_windowLimit_norm_le_majorant :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖W.G_limit (kernelID.coord s q)‖ ≤ kernelMajorant q

  /-- Summability of the weighted shared-kernel majorant. -/
  h_weightedKernelMajorant_summable :
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ * kernelMajorant q)

  /-- Concrete finite enumeration of prime-power pairs below cutoff. -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /-- Upper bound for exact enumerated prime-power mass. -/
  massUpper : ℕ → ℝ

  /-- Nonnegativity of the mass upper bound. -/
  h_massUpper_nonneg :
    ∀ n : ℕ, 0 ≤ massUpper n

  /-- Exact enumerated mass below `R_n` is bounded by `massUpper n`. -/
  h_exactMass_le_massUpper :
    ∀ n : ℕ,
      enumeratedPrimePowerMass massEnum ((alpha n).R) ≤
        massUpper n

  /--
  Lower bound for the compact D-window speed.
  -/
  speedLower : ℂ → ℕ → ℝ

  /-- Positivity of the speed lower bound. -/
  h_speedLower_pos :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 < speedLower s n

  /--
  The speed lower bound is below the compact-set D-window speed.
  -/
  h_speedLower_le_speed :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        speedLower s n ≤ windowSpeed.speed (coordSet s) n

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
Convert pure D-window speed API data into the previous limit-majorant package.
-/
def CanonicalPrimePowerDWindowSpeedAPILimitMajorantMassSpeedData.toLimitMajorantMassSpeedEstimateData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSpeedAPILimitMajorantMassSpeedData X) :
    CanonicalPrimePowerDWindowLimitMajorantMassSpeedEstimateData X :=
  { W := S.W
    alpha := S.alpha
    Kshared := S.Kshared

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R := S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := S.h_indices_subset_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg

    speedRate :=
      buildPrimePowerDWindowCompactSpeedRateDataFromWindowSpeedAPI
        S.kernelID
        S.coordSet
        S.h_coordSet_compact
        S.h_coord_mem
        S.windowSpeed

    h_windowLimit_norm_le_majorant := by
      intro s hs q
      exact S.h_windowLimit_norm_le_majorant s hs q

    h_weightedKernelMajorant_summable :=
      S.h_weightedKernelMajorant_summable

    massEnum := S.massEnum

    massUpper := S.massUpper
    h_massUpper_nonneg := S.h_massUpper_nonneg
    h_exactMass_le_massUpper := S.h_exactMass_le_massUpper

    speedLower := S.speedLower
    h_speedLower_pos := S.h_speedLower_pos
    h_speedLower_le_speed := S.h_speedLower_le_speed

    h_massUpper_div_speedLower_tendsto_zero :=
      S.h_massUpper_div_speedLower_tendsto_zero }

/--
Build `CanonicalPrimePowerExhaustionData` from pure D-window speed API data.
-/
def CanonicalPrimePowerDWindowSpeedAPILimitMajorantMassSpeedData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowSpeedAPILimitMajorantMassSpeedData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toLimitMajorantMassSpeedEstimateData.toExhaustionData

/--
Build `DBcanLimitData` directly from pure D-window speed API data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowSpeedAPI
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSpeedAPILimitMajorantMassSpeedData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowLimitMajorant
    X
    S.toLimitMajorantMassSpeedEstimateData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once pure D-window speed API data is supplied.
-/
theorem canonicalPrimePowerDWindowSpeedAPI_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowSpeedAPILimitMajorantMassSpeedData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowSpeedAPI X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowLimitMajorant_h_Bcan_matches_tsum
      X
      S.toLimitMajorantMassSpeedEstimateData
      s
      hs

end

end RHFormalization
