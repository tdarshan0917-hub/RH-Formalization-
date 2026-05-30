import RHFormalization.CanonicalPrimePowerDWindowKernelEstimate

/-!
# RHFormalization.CanonicalPrimePowerDWindowRateEstimate

Quantitative D-window rate estimate for active prime-power kernels.

This is not an RH endpoint.

The previous file proved the qualitative/eventual version:

  D.CANONICAL-WINDOW compact-uniform convergence
    ⇒ eventual active-index kernel-window error.

The R-cutoff estimate package, however, needs a quantitative rate field:

  ‖Kstage_n q.center s - Kshared q.center s‖ ≤ windowError n

for all active indices.  This file isolates exactly the quantitative
D.CANONICAL-WINDOW estimate needed to fill that field.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Quantitative D-window kernel estimate.

If the finite-stage prime-power kernel is represented by the D-window stage
kernel, the shared kernel is represented by the D-window limit kernel, and the
D-window stage/limit distance is bounded by `windowError n`, then the
prime-power kernel error is bounded by `windowError n`.
-/
theorem primePower_kernel_window_error_le_of_DWindow_rate
    (X : DFiniteStagePackageFromOperatorLayer)
    (W : DCanonicalWindowData)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (coord : PrimePowerPair → ℝ)
    (s : ℂ)
    (windowError : ℕ → ℝ)
    (h_stage_kernel_eq_window :
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s =
            W.gbar_stage (alpha n) (coord q))
    (h_shared_kernel_eq_limit :
      ∀ q : PrimePowerPair,
        Kshared q.center s =
          W.G_limit (coord q))
    (h_window_rate :
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          dist
            (W.gbar_stage (alpha n) (coord q))
            (W.G_limit (coord q)) ≤
              windowError n) :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        ‖X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
            Kshared q.center s‖ ≤
          windowError n := by
  intro n q hq

  have hdist :
      dist
        (W.gbar_stage (alpha n) (coord q))
        (W.G_limit (coord q)) ≤
          windowError n :=
    h_window_rate n q hq

  simpa
    [h_stage_kernel_eq_window n q hq,
     h_shared_kernel_eq_limit q,
     dist_eq_norm]
    using hdist

/--
Rate bridge data for one complex point `s`.

This is the exact local quantitative input needed to produce the active-index
kernel-window estimate.
-/
structure PrimePowerKernelWindowRateBridgeData
    (X : DFiniteStagePackageFromOperatorLayer)
    (W : DCanonicalWindowData)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ) where

  /-- Real displacement coordinate for each prime-power pair at point `s`. -/
  coord :
    PrimePowerPair → ℝ

  /-- Scalar window error rate at point `s`. -/
  windowError :
    ℕ → ℝ

  /--
  The finite-stage prime-power kernel is represented by the D-window stage
  kernel.
  -/
  h_stage_kernel_eq_window :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s =
          W.gbar_stage (alpha n) (coord q)

  /--
  The shared prime-power kernel is represented by the D-window limit kernel.
  -/
  h_shared_kernel_eq_limit :
    ∀ q : PrimePowerPair,
      Kshared q.center s =
        W.G_limit (coord q)

  /--
  Quantitative D.CANONICAL-WINDOW rate bound.
  -/
  h_window_rate :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        dist
          (W.gbar_stage (alpha n) (coord q))
          (W.G_limit (coord q)) ≤
            windowError n

/--
Extract the active-index prime-power kernel-window estimate from rate bridge
data.
-/
theorem PrimePowerKernelWindowRateBridgeData.kernel_window_error_le
    {X : DFiniteStagePackageFromOperatorLayer}
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    {Kshared : CanonicalKernelC}
    {s : ℂ}
    (B : PrimePowerKernelWindowRateBridgeData X W alpha Kshared s) :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        ‖X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
            Kshared q.center s‖ ≤
          B.windowError n := by
  exact
    primePower_kernel_window_error_le_of_DWindow_rate
      X
      W
      alpha
      Kshared
      B.coord
      s
      B.windowError
      B.h_stage_kernel_eq_window
      B.h_shared_kernel_eq_limit
      B.h_window_rate

end

end RHFormalization
