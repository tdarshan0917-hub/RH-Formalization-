import RHFormalization.ArithmeticShiftedLaplaceDBcanClean

/-!
# ArithmeticShiftedLaplaceIntegratedManifest

This file records the clean integrated status of the shifted-Laplace arithmetic
D-side route.

It combines two already-green components:

1. Local finite-stage DExport from native quadratic-form nonnegativity `hnn`.
2. Clean DBcan/Bshared limit package for the shifted-Laplace arithmetic B-stage.

This is not an RH endpoint. It is the clean D-side manifest before feeding into
the global E/H/F spine.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter Metric
open scoped BigOperators Classical

/--
Clean local+limit manifest.

For a single finite stage, native shifted nonnegativity gives the corrected
local `PerturbedDExport`.

For the stage sequence, the clean shifted-Laplace arithmetic B-stages converge
to the clean DBcan limit object.
-/
theorem arithmeticShiftedLaplace_localDExport_and_cleanDBcan_manifest
    {N : ℕ}
    -- one local finite stage
    (n : ℕ)
    (μ₀ : Fin N → ℝ)
    (M₀ : ℝ)
    (hnn₀ :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y
            (primeOpCLM μ₀ (primeStageWeights (N := N) n) M₀ y)))
    (c : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (hVball : Metric.closedBall c r ⊆ shiftedLaplaceAbsConvRegion)
    -- full finite-stage sequence
    (μ : ℕ → Fin N → ℝ)
    (M : ℕ → ℝ)
    (hnn :
      ∀ k : ℕ,
        ∀ y : EuclideanSpace ℂ (Fin N),
          0 ≤ RCLike.re
            (inner ℂ y
              (primeOpCLM (μ k) (primeStageWeights (N := N) k) (M k) y)))
    (s : ℂ)
    (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    PerturbedDExport
      (μShift μ₀ M₀)
      (primePotential_isHermitian (primeStageWeights (N := N) n))
      (arithmeticShiftedLaplaceBStage
        (arithmeticPrimeOperatorDFiniteStage n μ₀ M₀ hnn₀))
      (Metric.closedBall c r)
    ∧
    Tendsto
      (fun k : ℕ =>
        arithmeticShiftedLaplaceBStage
          (arithmeticPrimeOperatorDFiniteStage k (μ k) (M k) (hnn k)) s)
      Filter.atTop
      (𝓝 (arithmeticShiftedLaplaceCleanDBcanLimitSigma1.Bcan s)) := by
  constructor
  · exact
      ArithmeticShiftedPrimeDExport_on_absConv_closedBall_from_hnn
        n μ₀ M₀ hnn₀ c r hr hVball
  · exact
      arithmeticPrimeShiftedLaplaceBStage_tendsto_cleanDBcan_sigma1
        μ M hnn s hs

#print axioms arithmeticShiftedLaplace_localDExport_and_cleanDBcan_manifest

end

end RHFormalization
