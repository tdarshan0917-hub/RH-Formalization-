import RHFormalization.CanonicalPrimePowerDWindowSpeedAPI

/-!
# RHFormalization.CanonicalPrimePowerDWindowExactWindowSpeed

Exact-window-speed version of the D-window speed API frontier.

This file is not an RH endpoint.

The previous frontier still carried an auxiliary `speedLower` satisfying

  speedLower s n ≤ windowSpeed.speed (coordSet s) n.

This file removes that layer by taking

  speedLower s n := windowSpeed.speed (coordSet s) n.

The remaining rate obligation becomes the direct estimate

  massUpper n / windowSpeed.speed (coordSet s) n → 0.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
D-window speed API data with no auxiliary speed lower bound.

The speed used in the mass/speed asymptotic is exactly the compact-set speed
exported by `DCanonicalWindowCompactSpeedAPI`.
-/
structure CanonicalPrimePowerDWindowExactWindowSpeedData
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
  Mass upper bound divided by the actual compact D-window speed tends to zero.
  -/
  h_massUpper_div_windowSpeed_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          massUpper n / windowSpeed.speed (coordSet s) n)
        Filter.atTop
        (𝓝 0)

/--
Convert exact-window-speed data into the previous speed-API frontier data.

This sets

  `speedLower s n := windowSpeed.speed (coordSet s) n`.
-/
def CanonicalPrimePowerDWindowExactWindowSpeedData.toSpeedAPILimitMajorantMassSpeedData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactWindowSpeedData X) :
    CanonicalPrimePowerDWindowSpeedAPILimitMajorantMassSpeedData X :=
  { W := S.W
    alpha := S.alpha
    Kshared := S.Kshared

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R := S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := S.h_indices_subset_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg

    kernelID := S.kernelID
    coordSet := S.coordSet
    h_coordSet_compact := S.h_coordSet_compact
    h_coord_mem := S.h_coord_mem

    windowSpeed := S.windowSpeed

    h_windowLimit_norm_le_majorant := S.h_windowLimit_norm_le_majorant
    h_weightedKernelMajorant_summable := S.h_weightedKernelMajorant_summable

    massEnum := S.massEnum
    massUpper := S.massUpper
    h_massUpper_nonneg := S.h_massUpper_nonneg
    h_exactMass_le_massUpper := S.h_exactMass_le_massUpper

    speedLower := fun s n =>
      S.windowSpeed.speed (S.coordSet s) n

    h_speedLower_pos := by
      intro s hs n
      exact
        S.windowSpeed.h_speed_pos
          (S.coordSet s)
          (S.h_coordSet_compact s hs)
          n

    h_speedLower_le_speed := by
      intro s hs n
      rfl

    h_massUpper_div_speedLower_tendsto_zero := by
      intro s hs
      exact S.h_massUpper_div_windowSpeed_tendsto_zero s hs }

/--
Build `CanonicalPrimePowerExhaustionData` from exact-window-speed data.
-/
def CanonicalPrimePowerDWindowExactWindowSpeedData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowExactWindowSpeedData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toSpeedAPILimitMajorantMassSpeedData.toExhaustionData

/--
Build `DBcanLimitData` directly from exact-window-speed data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactWindowSpeed
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactWindowSpeedData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowSpeedAPI
    X
    S.toSpeedAPILimitMajorantMassSpeedData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once exact-window-speed data is supplied.
-/
theorem canonicalPrimePowerDWindowExactWindowSpeed_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowExactWindowSpeedData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowExactWindowSpeed X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowSpeedAPI_h_Bcan_matches_tsum
      X
      S.toSpeedAPILimitMajorantMassSpeedData
      s
      hs

end

end RHFormalization
