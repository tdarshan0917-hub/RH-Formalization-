import RHFormalization.ArithmeticShiftedLaplaceCleanYTarget
import RHFormalization.DFHLimitConcrete

/-!
# ArithmeticShiftedLaplaceCleanDFHTarget

Exact remaining DFH target.

The clean B-side is done. The EFH spine now needs a full `DFHLimitData`
for the clean shifted-Laplace finite layer.

`DFHLimitData` requires compact-uniform convergence on every compact `K ⊆ Ω`.
The currently proved arithmetic convergence is pointwise on `RightHalfPlane 1`.
So the missing theorem is an Ω-compact convergence/continuation upgrade, not
another B-stage identity.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators Classical

/--
The corrected arithmetic stage sequence used by the clean shifted-Laplace route.
-/
noncomputable def arithmeticShiftedLaplaceCleanStageSeq
    {N : ℕ}
    (μ : ℕ → Fin N → ℝ)
    (M : ℕ → ℝ)
    (hnn :
      ∀ n : ℕ,
        ∀ y : EuclideanSpace ℂ (Fin N),
          0 ≤ RCLike.re
            (inner ℂ y
              (primeOpCLM (μ n) (primeStageWeights (N := N) n) (M n) y))) :
    ℕ → DFiniteStage :=
  fun n => arithmeticPrimeOperatorDFiniteStage n (μ n) (M n) (hnn n)

/--
The exact missing Ω-compact DFH target.

This is the continuation/uniform-convergence input needed before a full clean
`Y : DDetailedConstructionWithOperatorLegality` can be built.
-/
structure ArithmeticShiftedLaplaceCleanDFHOmegaCompactTarget
    {N : ℕ}
    (μ : ℕ → Fin N → ℝ)
    (M : ℕ → ℝ)
    (hnn :
      ∀ n : ℕ,
        ∀ y : EuclideanSpace ℂ (Fin N),
          0 ≤ RCLike.re
            (inner ℂ y
              (primeOpCLM (μ n) (primeStageWeights (N := N) n) (M n) y))) where
  FH : ℂ → ℂ

  h_FH_holo :
    HolomorphicOnC FH Ω

  h_F_stage_to_FH :
    ∀ K : Set ℂ,
      IsCompact K →
      K ⊆ Ω →
        ∀ ε : ℝ,
          0 < ε →
            ∀ᶠ n in Filter.atTop,
              ∀ s : ℂ,
                s ∈ K →
                  dist
                    (arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1.toStagePackage.F_stage
                      (arithmeticShiftedLaplaceCleanStageSeq μ M hnn n)
                      s)
                    (FH s) < ε

/--
Once the Ω-compact target is supplied, it gives the required `DFHLimitData`.
-/
noncomputable def ArithmeticShiftedLaplaceCleanDFHOmegaCompactTarget.toDFH
    {N : ℕ}
    {μ : ℕ → Fin N → ℝ}
    {M : ℕ → ℝ}
    {hnn :
      ∀ n : ℕ,
        ∀ y : EuclideanSpace ℂ (Fin N),
          0 ≤ RCLike.re
            (inner ℂ y
              (primeOpCLM (μ n) (primeStageWeights (N := N) n) (M n) y))}
    (T : ArithmeticShiftedLaplaceCleanDFHOmegaCompactTarget μ M hnn) :
    DFHLimitData
      arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1.toStagePackage :=
  buildDFHLimitDataFromCompactUniform
    arithmeticShiftedLaplaceCleanFiniteOperatorLayerSigma1.toStagePackage
    (arithmeticShiftedLaplaceCleanStageSeq μ M hnn)
    T.FH
    T.h_FH_holo
    T.h_F_stage_to_FH

#print axioms arithmeticShiftedLaplaceCleanStageSeq
#print axioms ArithmeticShiftedLaplaceCleanDFHOmegaCompactTarget
#print axioms ArithmeticShiftedLaplaceCleanDFHOmegaCompactTarget.toDFH

end

end RHFormalization
