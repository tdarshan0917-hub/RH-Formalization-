import RHFormalization.CanonicalPrimePowerSharedKernelMajorant

/-!
# RHFormalization.CanonicalPrimePowerProductWindowError

Product window-error control for the canonical prime-power package.

This is not an RH endpoint.

The previous `CanonicalPrimePowerSharedKernelMajorantData` path still used a
uniform finite-mass bound

  ∑ q in indices(alpha n), ‖q.weightC‖ ≤ weightMassBound.

For the prime-weighted package, this may be too strong over exhausting prime
powers. The right Appendix-D-shaped condition is weaker and sharper:

  (∑ q in indices(alpha n), ‖q.weightC‖) * windowError s n → 0.

This file therefore replaces the uniform mass-bound assumption by a product
decay assumption.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the unweighted kernel-window error is bounded by `windowError n`, and the
finite weighted mass times `windowError n` tends to zero, then the actual finite
weighted kernel-error sum tends to zero.

This is the product-decay version of the D.CANONICAL-WINDOW estimate.
-/
theorem actual_kernel_error_sum_tendsto_zero_of_weightC_window_product
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (windowError : ℕ → ℝ)
    (h_windowError_nonneg :
      ∀ n : ℕ, 0 ≤ windowError n)
    (h_weightC_window_product_tendsto_zero :
      Tendsto
        (fun n : ℕ =>
          ((X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair => ‖q.weightC‖)) *
              windowError n)
        Filter.atTop
        (𝓝 0))
    (h_kernel_window_error_le :
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          ‖X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
              Kshared q.center s‖ ≤
            windowError n) :
    Tendsto
      (fun n : ℕ =>
        (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair =>
            canonicalPrimePowerActualTermError
              X
              alpha
              Kshared
              s
              n
              q))
      Filter.atTop
      (𝓝 0) := by
  exact
    real_tendsto_zero_of_nonneg_bound
      (u := fun n : ℕ =>
        (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair =>
            canonicalPrimePowerActualTermError
              X
              alpha
              Kshared
              s
              n
              q))
      (b := fun n : ℕ =>
        ((X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair => ‖q.weightC‖)) *
            windowError n)
      (by
        intro n
        exact
          Finset.sum_nonneg
            (fun q hq =>
              norm_nonneg _))
      (by
        intro n

        let I : Finset PrimePowerPair :=
          X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

        calc
          I.sum
              (fun q : PrimePowerPair =>
                canonicalPrimePowerActualTermError
                  X
                  alpha
                  Kshared
                  s
                  n
                  q)
              ≤
            I.sum
              (fun q : PrimePowerPair =>
                ‖q.weightC‖ * windowError n) := by
              exact
                Finset.sum_le_sum
                  (fun q hq =>
                    canonicalPrimePowerActualTermError_le_weight_norm_mul_window
                      X
                      alpha
                      Kshared
                      s
                      n
                      q
                      (windowError n)
                      (h_kernel_window_error_le n q hq))
          _ =
            (I.sum (fun q : PrimePowerPair => ‖q.weightC‖)) *
              windowError n := by
              simpa using
                (Finset.sum_mul
                  (s := I)
                  (f := fun q : PrimePowerPair => ‖q.weightC‖)
                  (a := windowError n)).symm)
      (by
        intro n
        exact
          mul_nonneg
            (Finset.sum_nonneg
              (fun q hq => norm_nonneg q.weightC))
            (h_windowError_nonneg n))
      h_weightC_window_product_tendsto_zero

/--
Product-window data for the canonical prime-power package.

Compared with `CanonicalPrimePowerSharedKernelMajorantData`, this removes the
uniform finite mass bound and replaces it with the weaker product condition

  `(finite weight mass) * windowError → 0`.
-/
structure CanonicalPrimePowerProductWindowErrorData
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
  Scalar window error. It may depend on `s`, but it is controlled through the
  product-decay condition below.
  -/
  windowError : ℂ → ℕ → ℝ

  /-- Nonnegativity of the window error. -/
  h_windowError_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ windowError s n

  /--
  Product-decay condition replacing the previous uniform mass bound.
  -/
  h_weightC_window_product_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          ((X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair => ‖q.weightC‖)) *
              windowError s n)
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
Convert product-window data directly into actual-kernel-error data.

This bypasses the too-strong uniform mass-bound branch.
-/
def CanonicalPrimePowerProductWindowErrorData.toActualKernelErrorData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerProductWindowErrorData X) :
    CanonicalPrimePowerActualKernelErrorData X :=
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

    h_actual_error_sum_tendsto_zero := by
      intro s hs
      exact
        actual_kernel_error_sum_tendsto_zero_of_weightC_window_product
          X
          S.alpha
          S.Kshared
          s
          (S.windowError s)
          (S.h_windowError_nonneg s hs)
          (S.h_weightC_window_product_tendsto_zero s hs)
          (S.h_kernel_window_error_le s hs) }

/--
Build `CanonicalPrimePowerExhaustionData` from product-window error data.
-/
def CanonicalPrimePowerProductWindowErrorData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerProductWindowErrorData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toActualKernelErrorData.toExhaustionData

/--
Build `DBcanLimitData` directly from product-window error data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerProductWindowError
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerProductWindowErrorData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerActualKernelError
    X
    S.toActualKernelErrorData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once product-window error data is supplied.
-/
theorem canonicalPrimePowerProductWindowError_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerProductWindowErrorData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerProductWindowError X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerActualKernelError_h_Bcan_matches_tsum
      X
      S.toActualKernelErrorData
      s
      hs

end

end RHFormalization
