import RHFormalization.CanonicalPrimePowerKernelErrorBound

/-!
# RHFormalization.CanonicalPrimePowerFiniteKernelErrorSum

Finite-sum kernel-error estimate for the canonical prime-power package.

This is not an RH endpoint.

The previous file reduced the D/H convergence problem to a scalar norm bound

  ‖stage kernel error n‖ ≤ errorBound n.

This file reduces that single large estimate to a finite sum of pointwise
prime-power kernel errors:

  ‖∑ q in I, weighted kernel error q‖
    ≤ ∑ q in I, termError q
    ≤ errorBound n.

This is the Lean-facing D.CANONICAL-WINDOW finite weighted-error shape.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Finite-sum norm estimate for the canonical prime-power stage-kernel error.

This is pure finite-sum algebra plus the triangle inequality.
-/
theorem finiteCanonicalPrimePowerPackage_kernel_error_norm_le_of_termError_sum
    (I : Finset PrimePowerPair)
    (Kstage Kshared : CanonicalKernelC)
    (s : ℂ)
    (termError : PrimePowerPair → ℝ)
    (errorBound : ℝ)
    (hterm :
      ∀ q : PrimePowerPair,
        q ∈ I →
          ‖q.weightC * Kstage q.center s -
            q.weightC * Kshared q.center s‖ ≤ termError q)
    (hsum :
      I.sum (fun q : PrimePowerPair => termError q) ≤ errorBound) :
    ‖finiteCanonicalPrimePowerPackage I Kstage s -
        I.sum
          (fun q : PrimePowerPair =>
            q.weightC * Kshared q.center s)‖ ≤
      errorBound := by
  classical

  have hrewrite :
      finiteCanonicalPrimePowerPackage I Kstage s -
          I.sum
            (fun q : PrimePowerPair =>
              q.weightC * Kshared q.center s)
        =
      I.sum
        (fun q : PrimePowerPair =>
          q.weightC * Kstage q.center s -
            q.weightC * Kshared q.center s) := by
    dsimp [finiteCanonicalPrimePowerPackage]
    simpa using
      (Finset.sum_sub_distrib
        (s := I)
        (f := fun q : PrimePowerPair =>
          q.weightC * Kstage q.center s)
        (g := fun q : PrimePowerPair =>
          q.weightC * Kshared q.center s)).symm

  calc
    ‖finiteCanonicalPrimePowerPackage I Kstage s -
        I.sum
          (fun q : PrimePowerPair =>
            q.weightC * Kshared q.center s)‖
        =
      ‖I.sum
        (fun q : PrimePowerPair =>
          q.weightC * Kstage q.center s -
            q.weightC * Kshared q.center s)‖ := by
        rw [hrewrite]
    _ ≤
      I.sum
        (fun q : PrimePowerPair =>
          ‖q.weightC * Kstage q.center s -
            q.weightC * Kshared q.center s‖) := by
        exact
          norm_sum_le
            (s := I)
            (f := fun q : PrimePowerPair =>
              q.weightC * Kstage q.center s -
                q.weightC * Kshared q.center s)
    _ ≤
      I.sum (fun q : PrimePowerPair => termError q) := by
        exact
          Finset.sum_le_sum
            (fun q hq => hterm q hq)
    _ ≤ errorBound := hsum

/--
Finite-term error data for the concrete canonical prime-power package.

Compared with `CanonicalPrimePowerKernelErrorBoundData`, this removes the large
field

  `h_stage_kernel_error_norm_le`

and replaces it by pointwise finite-term bounds plus a finite sum estimate.
-/
structure CanonicalPrimePowerFiniteKernelErrorData
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
  Pointwise finite-term kernel error bound.
  -/
  termError : ℂ → ℕ → PrimePowerPair → ℝ

  /--
  Each weighted stage/shared kernel discrepancy is bounded by the corresponding
  finite-term error.
  -/
  h_termError_bound :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          ‖q.weightC *
              X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
            q.weightC * Kshared q.center s‖ ≤
              termError s n q

  /--
  The finite sum of term errors is bounded by the scalar error bound.
  -/
  h_termError_sum_le_errorBound :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair => termError s n q) ≤
            errorBound s n

/--
Convert finite-term kernel-error data into the previous scalar-bound data.

This discharges `h_stage_kernel_error_norm_le` using the finite-sum triangle
inequality.
-/
def CanonicalPrimePowerFiniteKernelErrorData.toKernelErrorBoundData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerFiniteKernelErrorData X) :
    CanonicalPrimePowerKernelErrorBoundData X :=
  { alpha := S.alpha
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains
    majorant := S.majorant
    h_majorant_nonneg := S.h_majorant_nonneg
    h_term_norm_le_majorant := S.h_term_norm_le_majorant
    h_majorant_summable := S.h_majorant_summable
    errorBound := S.errorBound
    h_errorBound_nonneg := S.h_errorBound_nonneg
    h_errorBound_tendsto_zero := S.h_errorBound_tendsto_zero
    h_stage_kernel_error_norm_le := by
      intro s hs n

      simpa [canonicalPrimePowerStageKernelError] using
        finiteCanonicalPrimePowerPackage_kernel_error_norm_le_of_termError_sum
          (I :=
            X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n))
          (Kstage :=
            X.toFiniteCanonicalPrimePowerFormula.kernel (S.alpha n))
          (Kshared := S.Kshared)
          (s := s)
          (termError := S.termError s n)
          (errorBound := S.errorBound s n)
          (fun q hq =>
            S.h_termError_bound s hs n q hq)
          (S.h_termError_sum_le_errorBound s hs n) }

/--
Build `CanonicalPrimePowerExhaustionData` from finite-term kernel-error data.
-/
def CanonicalPrimePowerFiniteKernelErrorData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerFiniteKernelErrorData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toKernelErrorBoundData.toExhaustionData

/--
Build `DBcanLimitData` directly from finite-term kernel-error data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerFiniteKernelError
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerFiniteKernelErrorData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerKernelErrorBound
    X
    S.toKernelErrorBoundData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once finite-term kernel-error data is supplied.
-/
theorem canonicalPrimePowerFiniteKernelError_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerFiniteKernelErrorData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerFiniteKernelError X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerKernelErrorBound_h_Bcan_matches_tsum
      X
      S.toKernelErrorBoundData
      s
      hs

end

end RHFormalization
