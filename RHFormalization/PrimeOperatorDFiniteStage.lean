import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.PrimeNativeStageAssembly
import RHFormalization.PrimePerturbedFStage

/-!
# PrimeOperatorDFiniteStage

This file replaces the zero/free D-stage operator slot with the real
prime-perturbed operator stage.

It deliberately reuses the proven prime-power active-index machinery from
`primePowerStage`, but swaps the two fake fields:

* `native := zeroNativeStage`
* `appendixDFiniteFStage := fun _ => 0`

for the real prime operator:

* `native := primeNativeStage μ w M hnn`
* `appendixDFiniteFStage := primePerturbedFStage μ w`

This is a bridge file, not the final D.EXPORT bound.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

variable {N : ℕ}

/--
The real prime-operator DFiniteStage at cutoff level `n`.

This keeps the already-proven prime-power enumeration/spike data from
`primePowerStage n`, but replaces the native operator and F-stage by the
prime-perturbed operator.
-/
noncomputable def primeOperatorDFiniteStage
    (n : ℕ)
    (μ : Fin N → ℝ)
    (w : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re (inner ℂ y (primeOpCLM μ w M y))) :
    DFiniteStage :=
  { primePowerStage n with
    E := EuclideanSpace ℂ (Fin N)
    instNormed := inferInstance
    instInner := inferInstance
    instComplete := inferInstance
    native := primeNativeStage μ w M hnn
    appendixDFiniteFStage := primePerturbedFStage μ w }

/--
The real prime-operator stage has the correct F-stage:
not zero, not free, but the prime-perturbed resolvent trace.
-/
theorem primeOperatorDFiniteStage_F_stage
    (n : ℕ)
    (μ : Fin N → ℝ)
    (w : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re (inner ℂ y (primeOpCLM μ w M y))) :
    (primeOperatorDFiniteStage n μ w M hnn).appendixDFiniteFStage =
      primePerturbedFStage μ w := by
  rfl

/--
The cutoff is inherited from `primePowerStage`.
-/
theorem primeOperatorDFiniteStage_R
    (n : ℕ)
    (μ : Fin N → ℝ)
    (w : Fin N → ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re (inner ℂ y (primeOpCLM μ w M y))) :
    (primeOperatorDFiniteStage n μ w M hnn).R = (n : ℝ) + 1 := by
  rfl

#print axioms primeOperatorDFiniteStage
#print axioms primeOperatorDFiniteStage_F_stage
#print axioms primeOperatorDFiniteStage_R

end

end RHFormalization
