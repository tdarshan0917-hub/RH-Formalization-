import RHFormalization.CanonicalPrimePowerWindowMassError

/-!
# RHFormalization.CanonicalPrimePowerUniformWindowError

Uniform kernel-window error for the canonical prime-power package.

This is not an RH endpoint.

The previous layer reduced the actual finite weighted kernel-error sum to a
mass/window estimate:

  actual weighted error at q
    ≤ weightMass q * windowError s n.

This file removes the abstract `weightMass` function by choosing the natural
mass

  weightMass q := ‖q.weightC‖

and reducing the pointwise weighted estimate to the unweighted kernel-window
estimate

  ‖Kstage_n q.center s - Kshared q.center s‖ ≤ windowError s n.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Pure weighted-kernel norm estimate.

If the unweighted kernel discrepancy is bounded by `ε`, then the weighted
prime-power discrepancy is bounded by `‖q.weightC‖ * ε`.
-/
theorem weighted_kernel_error_norm_le_weight_norm_mul
    (q : PrimePowerPair)
    (Kstage Kshared : CanonicalKernelC)
    (s : ℂ)
    (ε : ℝ)
    (hkernel :
      ‖Kstage q.center s - Kshared q.center s‖ ≤ ε) :
    ‖q.weightC * Kstage q.center s -
        q.weightC * Kshared q.center s‖ ≤
      ‖q.weightC‖ * ε := by
  have hfactor :
      q.weightC * Kstage q.center s -
          q.weightC * Kshared q.center s =
        q.weightC * (Kstage q.center s - Kshared q.center s) := by
    rw [mul_sub]

  calc
    ‖q.weightC * Kstage q.center s -
        q.weightC * Kshared q.center s‖
        =
      ‖q.weightC * (Kstage q.center s - Kshared q.center s)‖ := by
        rw [hfactor]
    _ =
      ‖q.weightC‖ * ‖Kstage q.center s - Kshared q.center s‖ := by
        rw [norm_mul]
    _ ≤
      ‖q.weightC‖ * ε := by
        exact
          mul_le_mul_of_nonneg_left
            hkernel
            (norm_nonneg q.weightC)

/--
Specialized version for the actual term-error object.
-/
theorem canonicalPrimePowerActualTermError_le_weight_norm_mul_window
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (n : ℕ)
    (q : PrimePowerPair)
    (windowError : ℝ)
    (hkernel :
      ‖X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
          Kshared q.center s‖ ≤
        windowError) :
    canonicalPrimePowerActualTermError X alpha Kshared s n q ≤
      ‖q.weightC‖ * windowError := by
  simpa [canonicalPrimePowerActualTermError] using
    weighted_kernel_error_norm_le_weight_norm_mul
      q
      (X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n))
      Kshared
      s
      windowError
      hkernel

/--
Uniform-window data for the canonical prime-power actual kernel error.

Compared with `CanonicalPrimePowerWindowMassErrorData`, this removes the abstract
`weightMass` function and replaces it by the natural finite mass

  `‖q.weightC‖`.

The remaining pointwise window estimate is now unweighted.
-/
structure CanonicalPrimePowerUniformWindowErrorData
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

  /-- Nonnegativity of the shared-series majorant. -/
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

  /-- Summability of the shared-series majorant. -/
  h_majorant_summable :
    Summable majorant

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
Convert uniform-window data into the previous window/mass data.

The abstract mass is chosen as `‖q.weightC‖`, and the weighted pointwise estimate
is proved from the unweighted kernel-window estimate.
-/
def CanonicalPrimePowerUniformWindowErrorData.toWindowMassErrorData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerUniformWindowErrorData X) :
    CanonicalPrimePowerWindowMassErrorData X :=
  { alpha := S.alpha
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains
    majorant := S.majorant
    h_majorant_nonneg := S.h_majorant_nonneg
    h_term_norm_le_majorant := S.h_term_norm_le_majorant
    h_majorant_summable := S.h_majorant_summable

    weightMass := fun q : PrimePowerPair => ‖q.weightC‖
    h_weightMass_nonneg := by
      intro q
      exact norm_nonneg q.weightC

    weightMassBound := S.weightMassBound
    h_weightMassBound_nonneg := S.h_weightMassBound_nonneg
    h_weightMass_sum_le_bound := S.h_weightC_mass_sum_le_bound

    windowError := S.windowError
    h_windowError_nonneg := S.h_windowError_nonneg
    h_windowError_tendsto_zero := S.h_windowError_tendsto_zero

    h_actualTermError_le_window := by
      intro s hs n q hq
      exact
        canonicalPrimePowerActualTermError_le_weight_norm_mul_window
          X
          S.alpha
          S.Kshared
          s
          n
          q
          (S.windowError s n)
          (S.h_kernel_window_error_le s hs n q hq) }

/--
Build `CanonicalPrimePowerExhaustionData` from uniform-window error data.
-/
def CanonicalPrimePowerUniformWindowErrorData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerUniformWindowErrorData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toWindowMassErrorData.toExhaustionData

/--
Build `DBcanLimitData` directly from uniform-window error data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerUniformWindowError
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerUniformWindowErrorData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerWindowMassError
    X
    S.toWindowMassErrorData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once uniform-window error data is supplied.
-/
theorem canonicalPrimePowerUniformWindowError_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerUniformWindowErrorData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerUniformWindowError X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerWindowMassError_h_Bcan_matches_tsum
      X
      S.toWindowMassErrorData
      s
      hs

end

end RHFormalization
