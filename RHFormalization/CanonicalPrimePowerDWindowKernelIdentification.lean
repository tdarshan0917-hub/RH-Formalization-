import RHFormalization.CanonicalPrimePowerDWindowRateMassGrowth

/-!
# RHFormalization.CanonicalPrimePowerDWindowKernelIdentification

Kernel-identification layer for the D-window-rate mass-growth package.

This file is not an RH endpoint.

It separates the structural kernel-identification obligations from the genuinely
analytic D-window rate estimate.

After this file, the remaining D-window work is concentrated in the quantitative
rate estimate

  dist (W.gbar_stage (alpha n) (coord s q))
       (W.G_limit (coord s q)) ≤ windowError s n.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Structural identification data for the finite-stage and shared prime-power
kernels with the D-window kernels.
-/
structure PrimePowerDWindowKernelIdentificationData
    (X : DFiniteStagePackageFromOperatorLayer)
    (W : DCanonicalWindowData)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC) where

  /--
  Real displacement coordinate for the D-window kernel.
  -/
  coord :
    ℂ → PrimePowerPair → ℝ

  /--
  The finite-stage prime-power kernel is the D-window stage kernel.
  -/
  h_stage_kernel_eq_window :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s =
          W.gbar_stage (alpha n) (coord s q)

  /--
  The shared prime-power kernel is the D-window limit kernel.
  -/
  h_shared_kernel_eq_limit :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      Kshared q.center s =
        W.G_limit (coord s q)

/--
D-window-rate mass-growth data where the structural kernel identification is
supplied as one reusable package.
-/
structure CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData
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

  /-- Growth-window product tends to zero. -/
  h_massGrowth_window_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => massGrowth n * windowError s n)
        Filter.atTop
        (𝓝 0)

  /--
  Structural identification of prime-power kernels with D-window kernels.
  -/
  kernelID :
    PrimePowerDWindowKernelIdentificationData X W alpha Kshared

  /--
  Quantitative D.CANONICAL-WINDOW rate estimate.
  -/
  h_window_rate :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        dist
          (W.gbar_stage (alpha n) (kernelID.coord s q))
          (W.G_limit (kernelID.coord s q)) ≤
            windowError s n

/--
Convert identified-kernel data into the existing explicit D-window-rate /
mass-growth package.
-/
def CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData.toDWindowRateMassGrowthData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData X) :
    CanonicalPrimePowerDWindowRateMassGrowthData X :=
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
    h_massGrowth_window_tendsto_zero := S.h_massGrowth_window_tendsto_zero

    coord := S.kernelID.coord
    h_stage_kernel_eq_window := S.kernelID.h_stage_kernel_eq_window
    h_shared_kernel_eq_limit := S.kernelID.h_shared_kernel_eq_limit
    h_window_rate := S.h_window_rate }

/--
Build `CanonicalPrimePowerExhaustionData` from identified-kernel
D-window-rate/mass-growth data.
-/
def CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toDWindowRateMassGrowthData.toExhaustionData

/--
Build `DBcanLimitData` directly from identified-kernel
D-window-rate/mass-growth data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowIdentifiedRateMassGrowth
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowRateMassGrowth
    X
    S.toDWindowRateMassGrowthData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once identified-kernel D-window-rate/mass-growth data is supplied.
-/
theorem canonicalPrimePowerDWindowIdentifiedRateMassGrowth_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowIdentifiedRateMassGrowth X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowRateMassGrowth_h_Bcan_matches_tsum
      X
      S.toDWindowRateMassGrowthData
      s
      hs

end

end RHFormalization
