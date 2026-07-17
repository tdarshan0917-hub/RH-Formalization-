import RHFormalization.CanonicalPrimePowerDWindowKernelIdentification

/-!
# RHFormalization.CanonicalPrimePowerDWindowCompactRate

Compact-coordinate D-window rate layer.

This file is not an RH endpoint.

The previous frontier isolated the structural kernel identifications:

* stage kernel = `W.gbar_stage`;
* shared kernel = `W.G_limit`.

The remaining D-window estimate was the active-index rate

  dist (W.gbar_stage (alpha n) (coord s q))
       (W.G_limit (coord s q))
    ≤ windowError s n.

This file reduces that active-index rate to a compact-coordinate rate estimate:

* active prime-power coordinates lie in a compact real set;
* the D-window rate bound holds uniformly on that compact set.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Compact-coordinate D-window rate data.

This turns active-index window control into compact-set window control.
-/
structure PrimePowerDWindowCompactRateData
    (X : DFiniteStagePackageFromOperatorLayer)
    (W : DCanonicalWindowData)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (windowError : ℂ → ℕ → ℝ) where

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
  Quantitative D.CANONICAL-WINDOW rate bound on the compact coordinate set.
  -/
  h_compact_window_rate :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ a : ℝ,
      a ∈ coordSet s →
        dist
          (W.gbar_stage (alpha n) a)
          (W.G_limit a) ≤
            windowError s n

/--
Extract the active-index D-window rate from compact-coordinate rate data.
-/
theorem PrimePowerDWindowCompactRateData.active_window_rate
    {X : DFiniteStagePackageFromOperatorLayer}
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    {Kshared : CanonicalKernelC}
    {windowError : ℂ → ℕ → ℝ}
    (C : PrimePowerDWindowCompactRateData X W alpha Kshared windowError) :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        dist
          (W.gbar_stage (alpha n) (C.kernelID.coord s q))
          (W.G_limit (C.kernelID.coord s q)) ≤
            windowError s n := by
  intro s hs n q hq
  exact
    C.h_compact_window_rate
      s
      hs
      n
      (C.kernelID.coord s q)
      (C.h_coord_mem s hs n q hq)

/--
D-window compact-rate / mass-growth package.

Compared with `CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData`, this
removes the direct field

  `h_window_rate`

and replaces it by compact-coordinate D-window rate data.
-/
structure CanonicalPrimePowerDWindowCompactRateMassGrowthData
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
  Compact-coordinate D-window rate package.
  -/
  compactRate :
    PrimePowerDWindowCompactRateData X W alpha Kshared windowError

/--
Convert compact-coordinate rate data into the identified D-window-rate /
mass-growth package.
-/
def CanonicalPrimePowerDWindowCompactRateMassGrowthData.toIdentifiedRateMassGrowthData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowCompactRateMassGrowthData X) :
    CanonicalPrimePowerDWindowIdentifiedRateMassGrowthData X :=
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

    kernelID := S.compactRate.kernelID

    h_window_rate := by
      intro s hs n q hq
      exact S.compactRate.active_window_rate s hs n q hq }

/--
Build `CanonicalPrimePowerExhaustionData` from compact-coordinate D-window-rate
/ mass-growth data.
-/
def CanonicalPrimePowerDWindowCompactRateMassGrowthData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowCompactRateMassGrowthData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toIdentifiedRateMassGrowthData.toExhaustionData

/--
Build `DBcanLimitData` directly from compact-coordinate D-window-rate /
mass-growth data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowCompactRateMassGrowth
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowCompactRateMassGrowthData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerDWindowIdentifiedRateMassGrowth
    X
    S.toIdentifiedRateMassGrowthData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once compact-coordinate D-window-rate / mass-growth data is supplied.
-/
theorem canonicalPrimePowerDWindowCompactRateMassGrowth_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowCompactRateMassGrowthData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowCompactRateMassGrowth X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerDWindowIdentifiedRateMassGrowth_h_Bcan_matches_tsum
      X
      S.toIdentifiedRateMassGrowthData
      s
      hs

end

end RHFormalization
