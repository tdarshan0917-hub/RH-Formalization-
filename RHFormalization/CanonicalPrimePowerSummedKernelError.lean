import RHFormalization.CanonicalPrimePowerFiniteKernelErrorSum

/-!
# RHFormalization.CanonicalPrimePowerSummedKernelError

Finite summed-error realization of the canonical prime-power package.

This is not an RH endpoint.

The previous file reduced the stage-kernel error estimate to:

  pointwise term-error bounds
  + finite sum of term errors ≤ scalar errorBound.

This file removes the arbitrary scalar errorBound layer by defining the bound to
be exactly the finite sum of term errors:

  errorBound s n :=
    ∑ q in indices (alpha n), termError s n q.

Thus the remaining D.CANONICAL-WINDOW-shaped analytic target becomes the single
statement that this finite weighted error sum tends to zero.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Summed finite-term error data for the concrete canonical prime-power package.

Compared with `CanonicalPrimePowerFiniteKernelErrorData`, this removes the
separate scalar `errorBound` fields and replaces them by:

* nonnegativity of each finite term error;
* convergence to zero of the finite sum of term errors.
-/
structure CanonicalPrimePowerSummedKernelErrorData
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

  /-- Pointwise finite-term kernel error. -/
  termError : ℂ → ℕ → PrimePowerPair → ℝ

  /--
  Nonnegativity of finite-term errors on active finite-stage indices.
  -/
  h_termError_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          0 ≤ termError s n q

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
  Main D.CANONICAL-WINDOW-shaped finite weighted error target.

  The finite sum of term errors tends to zero on the D overlap half-plane.
  -/
  h_termError_sum_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair => termError s n q))
        Filter.atTop
        (𝓝 0)

/--
Convert summed finite-term error data into the previous finite-kernel-error data.

The scalar `errorBound` is chosen definitionally to be the finite sum of term
errors.
-/
def CanonicalPrimePowerSummedKernelErrorData.toFiniteKernelErrorData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSummedKernelErrorData X) :
    CanonicalPrimePowerFiniteKernelErrorData X :=
  { alpha := S.alpha
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains
    majorant := S.majorant
    h_majorant_nonneg := S.h_majorant_nonneg
    h_term_norm_le_majorant := S.h_term_norm_le_majorant
    h_majorant_summable := S.h_majorant_summable

    errorBound := fun s n =>
      (X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n)).sum
        (fun q : PrimePowerPair => S.termError s n q)

    h_errorBound_nonneg := by
      intro s hs n
      exact
        Finset.sum_nonneg
          (fun q hq =>
            S.h_termError_nonneg s hs n q hq)

    h_errorBound_tendsto_zero := by
      intro s hs
      exact S.h_termError_sum_tendsto_zero s hs

    termError := S.termError

    h_termError_bound := S.h_termError_bound

    h_termError_sum_le_errorBound := by
      intro s hs n
      exact le_rfl }

/--
Build `CanonicalPrimePowerExhaustionData` from summed finite-term kernel-error
data.
-/
def CanonicalPrimePowerSummedKernelErrorData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSummedKernelErrorData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toFiniteKernelErrorData.toExhaustionData

/--
Build `DBcanLimitData` directly from summed finite-term kernel-error data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerSummedKernelError
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSummedKernelErrorData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerFiniteKernelError
    X
    S.toFiniteKernelErrorData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once summed finite-term kernel-error data is supplied.
-/
theorem canonicalPrimePowerSummedKernelError_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSummedKernelErrorData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerSummedKernelError X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerFiniteKernelError_h_Bcan_matches_tsum
      X
      S.toFiniteKernelErrorData
      s
      hs

end

end RHFormalization
