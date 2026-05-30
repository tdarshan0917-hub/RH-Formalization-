import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration
import RHFormalization.CanonicalPrimePowerDWindowRateEstimate

/-!
# RHFormalization.CanonicalPrimePowerRCutoffRatePackaged

Packages the quantitative D-window rate bridge into the R-cutoff enumerated-mass
prime-power estimate package.

This is not an RH endpoint.

The previous file proved:

  D-window rate bound
    ⇒ active-index prime-power kernel-window estimate.

This file uses that theorem to discharge the `h_kernel_window_error_le` field
inside `CanonicalPrimePowerRCutoffEnumeratedMassWindowData`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
R-cutoff enumerated-mass data where the active-index kernel-window estimate is
not supplied directly.

Instead, it is derived from a pointwise quantitative D-window rate bridge.
-/
structure CanonicalPrimePowerRCutoffRatePackagedData
    (X : DFiniteStagePackageFromOperatorLayer) where

  /-- D-window data used to represent the finite and shared kernels. -/
  W : DCanonicalWindowData

  alpha : ℕ → DFiniteStage

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /--
  Concrete cutoff growth: the prime-power cutoff dominates the stage index.
  -/
  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

  /--
  The finite stage index set contains every prime-power pair whose center lies
  below the stage cutoff.
  -/
  h_indices_contains_of_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q.center ≤ (alpha n).R →
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  /--
  The finite stage index set contains only indices below the stage cutoff.
  -/
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

  /--
  Pointwise unweighted shared-kernel bound on the D overlap half-plane.
  -/
  h_sharedKernel_norm_le_majorant :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ q : PrimePowerPair,
        ‖Kshared q.center s‖ ≤ kernelMajorant q

  /--
  Summability of the weighted shared-kernel majorant.
  -/
  h_weightedKernelMajorant_summable :
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ * kernelMajorant q)

  /--
  Scalar window error used by the D-window rate bridge.
  -/
  windowError : ℂ → ℕ → ℝ

  /-- Nonnegativity of the window error. -/
  h_windowError_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ windowError s n

  /--
  Concrete finite enumeration of prime-power pairs below cutoff.
  -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /--
  Rate condition using the enumerated cutoff mass:

    `(∑ q in belowCutoff R_n, ‖q.weightC‖) * windowError_n → 0`.
  -/
  h_enumeratedMass_window_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (massEnum.belowCutoff ((alpha n).R)).sum
            (fun q : PrimePowerPair => ‖q.weightC‖)
          * windowError s n)
        Filter.atTop
        (𝓝 0)

  /--
  Pointwise D-window rate bridge at each `s` in the D overlap half-plane.
  -/
  rateBridge :
    ∀ s : ℂ,
      s ∈ RightHalfPlane X.toStagePackage.sigma0 →
        PrimePowerKernelWindowRateBridgeData X W alpha Kshared s

  /--
  The rate bridge's local window error agrees with the package-level
  `windowError`.
  -/
  h_rateBridge_windowError :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
      (rateBridge s hs).windowError n = windowError s n

/--
Convert rate-packaged data into the R-cutoff enumerated-mass package.

This discharges `h_kernel_window_error_le` using the quantitative D-window
rate bridge theorem.
-/
def CanonicalPrimePowerRCutoffRatePackagedData.toRCutoffEnumeratedMassWindowData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffRatePackagedData X) :
    CanonicalPrimePowerRCutoffEnumeratedMassWindowData X :=
  { alpha := S.alpha
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
    h_enumeratedMass_window_tendsto_zero :=
      S.h_enumeratedMass_window_tendsto_zero

    h_kernel_window_error_le := by
      intro s hs n q hq

      have hrate :
          ‖X.toFiniteCanonicalPrimePowerFormula.kernel (S.alpha n) q.center s -
              S.Kshared q.center s‖ ≤
            (S.rateBridge s hs).windowError n :=
        PrimePowerKernelWindowRateBridgeData.kernel_window_error_le
          (S.rateBridge s hs)
          n
          q
          hq

      simpa [S.h_rateBridge_windowError s hs n] using hrate }

/--
Build `CanonicalPrimePowerExhaustionData` from rate-packaged R-cutoff data.
-/
def CanonicalPrimePowerRCutoffRatePackagedData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffRatePackagedData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toRCutoffEnumeratedMassWindowData.toExhaustionData

/--
Build `DBcanLimitData` directly from rate-packaged R-cutoff data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerRCutoffRatePackaged
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffRatePackagedData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerRCutoffEnumeration
    X
    S.toRCutoffEnumeratedMassWindowData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once rate-packaged R-cutoff data is supplied.
-/
theorem canonicalPrimePowerRCutoffRatePackaged_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffRatePackagedData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerRCutoffRatePackaged X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerRCutoffEnumeration_h_Bcan_matches_tsum
      X
      S.toRCutoffEnumeratedMassWindowData
      s
      hs

end

end RHFormalization
