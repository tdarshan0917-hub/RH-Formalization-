import RHFormalization.CanonicalPrimePowerAsymptoticKernel

/-!
# RHFormalization.CanonicalPrimePowerKernelErrorBound

Quantitative kernel-error bound for the canonical prime-power package.

This is not an RH endpoint.

The previous file reduced the D/H finite-to-limit passage to an asymptotic
finite-stage kernel error:

  finiteCanonical(stage kernel)
    - finite partial sum(shared kernel)
      → 0.

This file replaces that direct `Tendsto` field by a quantitative scalar estimate:

  ‖kernel error n‖ ≤ errorBound n,
  errorBound n → 0.

This is the D.CANONICAL-WINDOW / finite weighted-error shape we actually want
from Appendix D.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
A complex-valued sequence tends to zero if its norm is bounded by a nonnegative
real sequence tending to zero.
-/
theorem complex_tendsto_zero_of_norm_bound
    {u : ℕ → ℂ}
    {errorBound : ℕ → ℝ}
    (h_nonneg : ∀ n : ℕ, 0 ≤ errorBound n)
    (h_bound : ∀ n : ℕ, ‖u n‖ ≤ errorBound n)
    (h_errorBound_zero : Tendsto errorBound Filter.atTop (𝓝 0)) :
    Tendsto u Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε

  have h_error_eventually :
      ∀ᶠ n in Filter.atTop, errorBound n < ε := by
    have hdist :=
      (Metric.tendsto_nhds.mp h_errorBound_zero) ε hε
    filter_upwards [hdist] with n hn

    have hdist_eq : dist (errorBound n) 0 = errorBound n := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (h_nonneg n)]

    simpa [hdist_eq] using hn

  filter_upwards [h_error_eventually] with n hn

  have hnorm_lt : ‖u n‖ < ε :=
    lt_of_le_of_lt (h_bound n) hn

  simpa [dist_eq_norm] using hnorm_lt

/--
The finite-stage kernel error at stage `n`, point `s`.

This is named so later Appendix-D files can target this exact expression rather
than duplicating a long term everywhere.
-/
noncomputable def canonicalPrimePowerStageKernelError
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (n : ℕ) : ℂ :=
  finiteCanonicalPrimePowerPackage
      (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n))
      (X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n))
      s
    -
  (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
    (fun q : PrimePowerPair =>
      q.weightC * Kshared q.center s)

/--
Bounded-error data for the concrete canonical prime-power package.

Compared with `CanonicalPrimePowerAsymptoticKernelMajorantData`, this removes the
direct `h_stage_kernel_error_tendsto_zero` field and replaces it with:

* a scalar error bound;
* nonnegativity of that bound;
* convergence of the bound to zero;
* a norm estimate for the actual finite weighted kernel error.
-/
structure CanonicalPrimePowerKernelErrorBoundData
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

  /-- Real nonnegative majorant for the shared prime-power kernel terms. -/
  majorant : PrimePowerPair → ℝ

  /-- Nonnegativity of the majorant. -/
  h_majorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ majorant q

  /--
  Pointwise norm bound for the shared prime-power kernel term on the D overlap
  half-plane.
  -/
  h_term_norm_le_majorant :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ q : PrimePowerPair,
        ‖q.weightC * Kshared q.center s‖ ≤ majorant q

  /-- Summability of the real majorant. -/
  h_majorant_summable :
    Summable majorant

  /--
  The finite weighted shared-kernel partial sums converge to the shared package.

  This is the support-aware replacement for full raw `PrimePowerPair`
  exhaustion. The scalar error bound below only controls the difference between
  the stage kernel sum and this shared-kernel partial sum; it does not by itself
  prove convergence of the shared-kernel partial sums.
  -/
  h_weighted_partial_tendsto :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
        Filter.atTop
        (𝓝 ((canonicalPrimePowerPackageFromKernelTsum
              X.toStagePackage.sigma0
              Kshared).Bshared s))

  /--
  Scalar error bound for the finite weighted kernel error.
  The bound may depend on `s`.
  -/
  errorBound : ℂ → ℕ → ℝ

  /-- Nonnegativity of the scalar error bound on the D overlap half-plane. -/
  h_errorBound_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ errorBound s n

  /-- The scalar error bound tends to zero on the D overlap half-plane. -/
  h_errorBound_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (errorBound s)
        Filter.atTop
        (𝓝 0)

  /--
  Quantitative D.CANONICAL-WINDOW-shaped bound for the finite weighted kernel
  error.
  -/
  h_stage_kernel_error_norm_le :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        ‖canonicalPrimePowerStageKernelError X alpha Kshared s n‖ ≤
          errorBound s n

/--
Convert quantitative bounded-error data into the previous asymptotic-kernel data.

This discharges `h_stage_kernel_error_tendsto_zero` using
`complex_tendsto_zero_of_norm_bound`.
-/
def CanonicalPrimePowerKernelErrorBoundData.toAsymptoticKernelMajorantData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerKernelErrorBoundData X) :
    CanonicalPrimePowerAsymptoticKernelMajorantData X :=
  { alpha := S.alpha
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains
    majorant := S.majorant
    h_majorant_nonneg := S.h_majorant_nonneg
    h_term_norm_le_majorant := S.h_term_norm_le_majorant
    h_majorant_summable := S.h_majorant_summable
    h_weighted_partial_tendsto := S.h_weighted_partial_tendsto
    h_stage_kernel_error_tendsto_zero := by
      intro s hs

      exact
        complex_tendsto_zero_of_norm_bound
          (u := canonicalPrimePowerStageKernelError X S.alpha S.Kshared s)
          (errorBound := S.errorBound s)
          (S.h_errorBound_nonneg s hs)
          (S.h_stage_kernel_error_norm_le s hs)
          (S.h_errorBound_tendsto_zero s hs) }

/--
Build `CanonicalPrimePowerExhaustionData` from quantitative bounded-error data.
-/
def CanonicalPrimePowerKernelErrorBoundData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerKernelErrorBoundData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toAsymptoticKernelMajorantData.toExhaustionData

/--
Build `DBcanLimitData` directly from quantitative bounded-error data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerKernelErrorBound
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerKernelErrorBoundData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerAsymptoticKernel
    X
    S.toAsymptoticKernelMajorantData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once quantitative bounded-error data is supplied.
-/
theorem canonicalPrimePowerKernelErrorBound_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerKernelErrorBoundData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerKernelErrorBound X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerAsymptoticKernel_h_Bcan_matches_tsum
      X
      S.toAsymptoticKernelMajorantData
      s
      hs

end

end RHFormalization
