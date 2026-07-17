import RHFormalization.PrimeOperatorDFiniteStage

/-!
# PrimeOperatorArithmeticWeights

This file removes the arbitrary-weight objection.

It instantiates the `w : Fin N → ℝ` in `primeOperatorDFiniteStage`
from the actual finite prime-power stage codes, using the existing
`ppDecode k).weightC` arithmetic package.

This still does not prove the zeta correspondence. It makes the operator
arithmetically instantiated instead of free in `w`.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

variable {N : ℕ}

/-- Real arithmetic weight attached to a Nat-coded prime-power spike. -/
noncomputable def ppWeightReal (k : ℕ) : ℝ :=
  ((ppDecode k).weightC).re

/--
Stage arithmetic weight vector.

For a finite Hilbert-space index `i : Fin N`, use the existing active
prime-power code set `ppStageCodes n`. Active codes get their decoded
prime-power weight; inactive coordinates get zero.
-/
noncomputable def primeStageWeights (n : ℕ) : Fin N → ℝ :=
  fun i =>
    if (i.val ∈ ppStageCodes n) then
      ppWeightReal i.val
    else
      0

/-- On active coordinates, the arithmetic weight is exactly the decoded prime-power weight. -/
theorem primeStageWeights_active
    (n : ℕ) (i : Fin N)
    (hi : i.val ∈ ppStageCodes n) :
    primeStageWeights n i = ppWeightReal i.val := by
  simp [primeStageWeights, hi]

/-- On inactive coordinates, the arithmetic weight is zero. -/
theorem primeStageWeights_inactive
    (n : ℕ) (i : Fin N)
    (hi : i.val ∉ ppStageCodes n) :
    primeStageWeights n i = 0 := by
  simp [primeStageWeights, hi]

/--
The prime-operator DFiniteStage with arithmetic weights, not arbitrary weights.

The only remaining analytic input here is the honest shift/nonnegativity
hypothesis `hnn`, now specialized to the arithmetic weight vector.
-/
noncomputable def arithmeticPrimeOperatorDFiniteStage
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y))) :
    DFiniteStage :=
  primeOperatorDFiniteStage n μ (primeStageWeights n) M hnn

/--
The arithmetic prime-operator stage has the correct nonzero F-stage:
the prime-perturbed resolvent with actual stage weights.
-/
theorem arithmeticPrimeOperatorDFiniteStage_F_stage
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y))) :
    (arithmeticPrimeOperatorDFiniteStage n μ M hnn).appendixDFiniteFStage =
      primePerturbedFStage μ (primeStageWeights n) := by
  rfl

/-- The cutoff is inherited from the prime-power stage. -/
theorem arithmeticPrimeOperatorDFiniteStage_R
    (n : ℕ)
    (μ : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re
          (inner ℂ y (primeOpCLM μ (primeStageWeights n) M y))) :
    (arithmeticPrimeOperatorDFiniteStage n μ M hnn).R = (n : ℝ) + 1 := by
  rfl

#print axioms ppWeightReal
#print axioms primeStageWeights
#print axioms primeStageWeights_active
#print axioms primeStageWeights_inactive
#print axioms arithmeticPrimeOperatorDFiniteStage
#print axioms arithmeticPrimeOperatorDFiniteStage_F_stage
#print axioms arithmeticPrimeOperatorDFiniteStage_R

end

end RHFormalization
