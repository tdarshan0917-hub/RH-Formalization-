import RHFormalization.CanonicalPrimePowerSummedKernelError

/-!
# RHFormalization.CanonicalPrimePowerActualKernelError

Actual weighted kernel-error realization of the canonical prime-power package.

This is not an RH endpoint.

The previous layer still carried an abstract `termError` together with
nonnegativity and pointwise bound fields. This file removes that abstraction by
defining the term error to be the actual weighted kernel discrepancy norm:

  ‖q.weightC * Kstage q.center s - q.weightC * Kshared q.center s‖.

After this file, the remaining D.CANONICAL-WINDOW estimate is exactly the
finite weighted kernel-error sum tending to zero.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The actual weighted prime-power kernel discrepancy at stage `n`, point `s`,
and prime-power index `q`.
-/
noncomputable def canonicalPrimePowerActualTermError
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (n : ℕ)
    (q : PrimePowerPair) : ℝ :=
  ‖q.weightC *
      X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
    q.weightC * Kshared q.center s‖

/--
Actual-kernel-error data for the concrete canonical prime-power package.

Compared with `CanonicalPrimePowerSummedKernelErrorData`, this removes:

* `termError`;
* `h_termError_nonneg`;
* `h_termError_bound`.

The only remaining kernel-error convergence input is the actual finite weighted
kernel-error sum tending to zero.
-/
structure CanonicalPrimePowerActualKernelErrorData
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
  Main D.CANONICAL-WINDOW-shaped finite weighted kernel-error target.

  The actual finite weighted kernel discrepancy sum tends to zero on the D
  overlap half-plane.
  -/
  h_actual_error_sum_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair =>
              canonicalPrimePowerActualTermError X alpha Kshared s n q))
        Filter.atTop
        (𝓝 0)

/--
Convert actual weighted kernel-error data into the previous summed-error data.

The abstract `termError` is chosen definitionally as the actual norm error.
-/
def CanonicalPrimePowerActualKernelErrorData.toSummedKernelErrorData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerActualKernelErrorData X) :
    CanonicalPrimePowerSummedKernelErrorData X :=
  { alpha := S.alpha
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains
    majorant := S.majorant
    h_majorant_nonneg := S.h_majorant_nonneg
    h_term_norm_le_majorant := S.h_term_norm_le_majorant
    h_majorant_summable := S.h_majorant_summable

    termError := fun s n q =>
      canonicalPrimePowerActualTermError X S.alpha S.Kshared s n q

    h_termError_nonneg := by
      intro s hs n q hq
      exact norm_nonneg _

    h_termError_bound := by
      intro s hs n q hq
      exact le_rfl

    h_termError_sum_tendsto_zero := by
      intro s hs
      exact S.h_actual_error_sum_tendsto_zero s hs }

/--
Build `CanonicalPrimePowerExhaustionData` from actual weighted kernel-error data.
-/
def CanonicalPrimePowerActualKernelErrorData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerActualKernelErrorData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toSummedKernelErrorData.toExhaustionData

/--
Build `DBcanLimitData` directly from actual weighted kernel-error data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerActualKernelError
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerActualKernelErrorData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerSummedKernelError
    X
    S.toSummedKernelErrorData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once actual weighted kernel-error data is supplied.
-/
theorem canonicalPrimePowerActualKernelError_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerActualKernelErrorData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerActualKernelError X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerSummedKernelError_h_Bcan_matches_tsum
      X
      S.toSummedKernelErrorData
      s
      hs

end

end RHFormalization
