-- SENTINEL: coscaled-net-v1
import RHFormalization.PrimeOperatorArithmeticWeights
import Mathlib

/-!
# ArithmeticPrimeCoScaledNet — the manuscript's ordered net (2026-07-16F)
The fourth taxonomy cell: undiluted F, dimension co-scaled with the cutoff.
`Nfun n` grows with the stage so the potential contains ALL active spikes
below cutoff n+1 (no Fin-N starvation). Pure wiring on the rfl-verified
`arithmeticPrimeOperatorDFiniteStage`; hnn is the manuscript's global-shift
positivity, carried as data. Consumer: sector bounds + SP2a/SP2b constructors.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **The co-scaled arithmetic prime net.** Stage n: real prime operator,
arithmetic weights `primeStageWeights n`, cutoff `n+1`, dimension `Nfun n`. -/
noncomputable def arithmeticPrimeNet
    (Nfun : ℕ → ℕ)
    (μ : ∀ n : ℕ, Fin (Nfun n) → ℝ)
    (M : ℝ)
    (hnn : ∀ n : ℕ, ∀ y : EuclideanSpace ℂ (Fin (Nfun n)),
      0 ≤ RCLike.re (inner ℂ y
        (primeOpCLM (μ n) (primeStageWeights (N := Nfun n) n) M y))) :
    ℕ → DFiniteStage :=
  fun n => arithmeticPrimeOperatorDFiniteStage n (μ n) M (hnn n)

/-- The net's F-stage is the genuine perturbed trace at co-scaled dimension. -/
theorem arithmeticPrimeNet_F_stage
    (Nfun : ℕ → ℕ) (μ : ∀ n, Fin (Nfun n) → ℝ) (M : ℝ)
    (hnn : ∀ n : ℕ, ∀ y : EuclideanSpace ℂ (Fin (Nfun n)),
      0 ≤ RCLike.re (inner ℂ y
        (primeOpCLM (μ n) (primeStageWeights (N := Nfun n) n) M y)))
    (n : ℕ) :
    (arithmeticPrimeNet Nfun μ M hnn n).appendixDFiniteFStage
      = primePerturbedFStage (μ n) (primeStageWeights (N := Nfun n) n) := rfl

/-- The net's cutoff is n+1. -/
theorem arithmeticPrimeNet_R
    (Nfun : ℕ → ℕ) (μ : ∀ n, Fin (Nfun n) → ℝ) (M : ℝ)
    (hnn : ∀ n : ℕ, ∀ y : EuclideanSpace ℂ (Fin (Nfun n)),
      0 ≤ RCLike.re (inner ℂ y
        (primeOpCLM (μ n) (primeStageWeights (N := Nfun n) n) M y)))
    (n : ℕ) :
    (arithmeticPrimeNet Nfun μ M hnn n).R = (n : ℝ) + 1 := rfl

#print axioms arithmeticPrimeNet
#print axioms arithmeticPrimeNet_F_stage
#print axioms arithmeticPrimeNet_R

end

end RHFormalization
