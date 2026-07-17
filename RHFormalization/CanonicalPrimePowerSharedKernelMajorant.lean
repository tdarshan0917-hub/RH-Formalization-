import RHFormalization.CanonicalPrimePowerUniformWindowError

/-!
# RHFormalization.CanonicalPrimePowerSharedKernelMajorant

Shared-kernel majorant layer for the canonical prime-power package.

This is not an RH endpoint.

The previous layer reduced the finite window error to the unweighted estimate

  ‖Kstage_n q.center s - Kshared q.center s‖ ≤ windowError s n.

It still carried an abstract majorant for the shared weighted series

  ‖q.weightC * Kshared q.center s‖ ≤ majorant q.

This file removes that abstraction by taking

  majorant q := ‖q.weightC‖ * kernelMajorant q,

where `kernelMajorant` bounds the unweighted shared kernel.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the unweighted shared kernel is bounded by `kernelMajorant q`, then the
weighted shared term is bounded by `‖q.weightC‖ * kernelMajorant q`.
-/
theorem weighted_shared_kernel_norm_le_weight_norm_mul_majorant
    (q : PrimePowerPair)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (kernelMajorant : PrimePowerPair → ℝ)
    (hkernel :
      ‖Kshared q.center s‖ ≤ kernelMajorant q) :
    ‖q.weightC * Kshared q.center s‖ ≤
      ‖q.weightC‖ * kernelMajorant q := by
  calc
    ‖q.weightC * Kshared q.center s‖
        =
      ‖q.weightC‖ * ‖Kshared q.center s‖ := by
        rw [norm_mul]
    _ ≤
      ‖q.weightC‖ * kernelMajorant q := by
        exact
          mul_le_mul_of_nonneg_left
            hkernel
            (norm_nonneg q.weightC)

/--
Shared-kernel majorant data for the canonical prime-power package.

Compared with `CanonicalPrimePowerUniformWindowErrorData`, this removes the
abstract weighted-series majorant fields and replaces them with:

* an unweighted shared-kernel majorant;
* summability of the weighted majorant `‖q.weightC‖ * kernelMajorant q`.
-/
structure CanonicalPrimePowerSharedKernelMajorantData
    (X : DFiniteStagePackageFromOperatorLayer) where
  alpha : ℕ → DFiniteStage

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /--
  Concrete finite-stage exhaustion: every prime-power index eventually appears
  in the finite stage index sets.
  -/
  h_indices_eventually_contains :
    ∀ q : PrimePowerPair,
      IsPrimePowerPair q →
      ∃ N : ℕ,
        ∀ n : ℕ,
          N ≤ n →
            q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  /--
  Unweighted majorant for the shared kernel.
  -/
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

  /-- Uniform bound for finite-stage weighted masses `∑ ‖q.weightC‖`. -/
  weightMassBound : ℝ

  /-- Nonnegativity of the uniform mass bound. -/
  h_weightMassBound_nonneg :
    0 ≤ weightMassBound

  /--
  The finite-stage index-set weight mass is uniformly bounded.
  -/
  h_weightC_mass_sum_le_bound :
    ∀ n : ℕ,
      (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
        (fun q : PrimePowerPair => ‖q.weightC‖) ≤
          weightMassBound

  /--
  Scalar window error. It may depend on `s`, but it must tend to zero for each
  `s` in the overlap half-plane.
  -/
  windowError : ℂ → ℕ → ℝ

  /-- Nonnegativity of the window error. -/
  h_windowError_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ windowError s n

  /-- The scalar window error tends to zero on the D overlap half-plane. -/
  h_windowError_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (windowError s)
        Filter.atTop
        (𝓝 0)

  /--
  Unweighted D.CANONICAL-WINDOW estimate on active finite-stage indices.
  -/
  h_kernel_window_error_le :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          ‖X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
              Kshared q.center s‖ ≤
            windowError s n

/--
Convert shared-kernel majorant data into the previous uniform-window data.

The abstract weighted-series majorant is chosen as

  `fun q => ‖q.weightC‖ * kernelMajorant q`.
-/
def CanonicalPrimePowerSharedKernelMajorantData.toUniformWindowErrorData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharedKernelMajorantData X) :
    CanonicalPrimePowerUniformWindowErrorData X :=
  { alpha := S.alpha
    Kshared := S.Kshared

    h_indices_eventually_contains := S.h_indices_eventually_contains

    majorant :=
      fun q : PrimePowerPair =>
        ‖q.weightC‖ * S.kernelMajorant q

    h_majorant_nonneg := by
      intro q
      exact
        mul_nonneg
          (norm_nonneg q.weightC)
          (S.h_kernelMajorant_nonneg q)

    h_term_norm_le_majorant := by
      intro s hs q
      exact
        weighted_shared_kernel_norm_le_weight_norm_mul_majorant
          q
          S.Kshared
          s
          S.kernelMajorant
          (S.h_sharedKernel_norm_le_majorant s hs q)

    h_majorant_summable :=
      S.h_weightedKernelMajorant_summable

    weightMassBound := S.weightMassBound
    h_weightMassBound_nonneg := S.h_weightMassBound_nonneg
    h_weightC_mass_sum_le_bound := S.h_weightC_mass_sum_le_bound

    windowError := S.windowError
    h_windowError_nonneg := S.h_windowError_nonneg
    h_windowError_tendsto_zero := S.h_windowError_tendsto_zero
    h_kernel_window_error_le := S.h_kernel_window_error_le }

/--
Build `CanonicalPrimePowerExhaustionData` from shared-kernel majorant data.
-/
def CanonicalPrimePowerSharedKernelMajorantData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharedKernelMajorantData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toUniformWindowErrorData.toExhaustionData

/--
Build `DBcanLimitData` directly from shared-kernel majorant data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerSharedKernelMajorant
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharedKernelMajorantData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerUniformWindowError
    X
    S.toUniformWindowErrorData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once shared-kernel majorant data is supplied.
-/
theorem canonicalPrimePowerSharedKernelMajorant_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharedKernelMajorantData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerSharedKernelMajorant X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerUniformWindowError_h_Bcan_matches_tsum
      X
      S.toUniformWindowErrorData
      s
      hs

end

end RHFormalization
