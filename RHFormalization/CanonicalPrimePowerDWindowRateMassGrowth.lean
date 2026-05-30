import RHFormalization.CanonicalPrimePowerEnumeratedMassGrowthRate

/-!
# RHFormalization.CanonicalPrimePowerDWindowRateMassGrowth

D-window-rate version of the R-cutoff / enumerated-mass / mass-growth package.

This file is not an RH endpoint.

The previous frontier still carried an abstract

  `rateBridge`

field. This file removes that abstraction and replaces it with the concrete
D-window data:

* a real displacement coordinate;
* identification of the stage kernel with `W.gbar_stage`;
* identification of the shared kernel with `W.G_limit`;
* a quantitative D-window rate bound.

These are the actual D.CANONICAL-WINDOW estimate fields.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
R-cutoff / mass-growth data with the D-window rate estimate written explicitly.

Compared with `CanonicalPrimePowerRCutoffRateMassGrowthData`, this removes:

* `rateBridge`;
* `h_rateBridge_windowError`.

It replaces them with the actual D-window rate ingredients.
-/
structure CanonicalPrimePowerDWindowRateMassGrowthData
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

  /-- Growth-window product tends to zero. -/
  h_massGrowth_window_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => massGrowth n * windowError s n)
        Filter.atTop
        (𝓝 0)

  /--
  Real displacement coordinate for the D-window kernel.

  For each complex point `s` and prime-power pair `q`, this gives the real
  window displacement coordinate used by `W.gbar_stage` and `W.G_limit`.
  -/
  coord :
    ℂ → PrimePowerPair → ℝ

  /--
  The finite-stage prime-power kernel is represented by the D-window stage
  kernel.
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
  The shared prime-power kernel is represented by the D-window limiting kernel.
  -/
  h_shared_kernel_eq_limit :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      Kshared q.center s =
        W.G_limit (coord s q)

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
          (W.gbar_stage (alpha n) (coord s q))
          (W.G_limit (coord s q)) ≤
            windowError s n

/--
Convert the explicit D-window-rate data into the previous rate-packaged data.

This constructs `rateBridge` from the concrete D-window identities and rate
estimate.
-/
def CanonicalPrimePowerDWindowRateMassGrowthData.toRCutoffRateMassGrowthData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowRateMassGrowthData X) :
    CanonicalPrimePowerRCutoffRateMassGrowthData X :=
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

    rateBridge := by
      intro s hs
      exact
        { coord := S.coord s
          windowError := S.windowError s
          h_stage_kernel_eq_window := by
            intro n q hq
            exact S.h_stage_kernel_eq_window s hs n q hq
          h_shared_kernel_eq_limit := by
            intro q
            exact S.h_shared_kernel_eq_limit s hs q
          h_window_rate := by
            intro n q hq
            exact S.h_window_rate s hs n q hq }

    h_rateBridge_windowError := by
      intro s hs n
      rfl }

/--
Build `CanonicalPrimePowerExhaustionData` from explicit D-window-rate /
mass-growth data.
-/
def CanonicalPrimePowerDWindowRateMassGrowthData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerDWindowRateMassGrowthData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toRCutoffRateMassGrowthData.toExhaustionData

/--
Build `DBcanLimitData` directly from explicit D-window-rate / mass-growth data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerDWindowRateMassGrowth
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowRateMassGrowthData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerRCutoffRateMassGrowth
    X
    S.toRCutoffRateMassGrowthData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once explicit D-window-rate / mass-growth data is supplied.
-/
theorem canonicalPrimePowerDWindowRateMassGrowth_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerDWindowRateMassGrowthData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerDWindowRateMassGrowth X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerRCutoffRateMassGrowth_h_Bcan_matches_tsum
      X
      S.toRCutoffRateMassGrowthData
      s
      hs

end

end RHFormalization
