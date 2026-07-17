import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.PerturbedResidual

/-!
# ArithmeticPrimeOperatorResidual

This file names the real correspondence frontier.

We now have the arithmetic prime-operator D-stage:

  arithmeticPrimeOperatorDFiniteStage

whose F-stage is

  primePerturbedFStage μ (primeStageWeights n).

The next object is the honest residual between that arithmetic operator F-stage
and an arbitrary comparison/zeta-side package `B`.

This does not prove the correspondence. It names the exact target.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

variable {N : ℕ}

/-- The arithmetic prime-operator F-stage at cutoff `n`. -/
noncomputable def arithmeticPrimeFStage
    (n : ℕ) (μ : Fin N → ℝ) : ℂ → ℂ :=
  primePerturbedFStage μ (primeStageWeights (N := N) n)

/-- The honest arithmetic prime-operator residual against a comparison package `B`. -/
noncomputable def arithmeticPrimeResidual
    (n : ℕ) (μ : Fin N → ℝ) (B : ℂ → ℂ) : ℂ → ℂ :=
  fun s => arithmeticPrimeFStage n μ s - B s

/--
The arithmetic residual is exactly the existing perturbed residual instantiated
with the arithmetic prime-stage weight vector.
-/
theorem arithmeticPrimeResidual_eq_perturbedResidual
    (n : ℕ) (μ : Fin N → ℝ) (B : ℂ → ℂ) (s : ℂ) :
    arithmeticPrimeResidual n μ B s =
      perturbedResidual μ
        (primePotential_isHermitian (primeStageWeights (N := N) n))
        B s := by
  rfl

/--
The honest D.EXPORT/correspondence target for the arithmetic prime operator.

This is the next frontier: prove this for the correct `B` package and Ω-compact `K`.
-/
def ArithmeticPrimeDExport
    (n : ℕ) (μ : Fin N → ℝ) (B : ℂ → ℂ) (K : Set ℂ) : Prop :=
  PerturbedDExport μ
    (primePotential_isHermitian (primeStageWeights (N := N) n))
    B K

#print axioms arithmeticPrimeFStage
#print axioms arithmeticPrimeResidual
#print axioms arithmeticPrimeResidual_eq_perturbedResidual
#print axioms ArithmeticPrimeDExport

end

end RHFormalization
