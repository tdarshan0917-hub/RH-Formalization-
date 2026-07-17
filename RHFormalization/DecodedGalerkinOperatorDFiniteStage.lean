import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.DecodedGalerkinNativeStageAssembly
import RHFormalization.DecodedGalerkinPerturbedFStage

/-!
# PrimeOperatorDFiniteStage

This file replaces the zero/free D-stage operator slot with the real
prime-perturbed operator stage.

It deliberately reuses the proven prime-power active-index machinery from
`primePowerStage`, but swaps the two fake fields:

* `native := zeroNativeStage`
* `appendixDFiniteFStage := fun _ => 0`

for the real prime operator:

* `native := decodedGalerkinNativeStage μ δ qs w L M hnn`
* `appendixDFiniteFStage := decodedGalerkinPerturbedFStage (N := N) μ δ qs w L`

This is a bridge file, not the final D.EXPORT bound.
-/

-- SENTINEL: decoded-operator-dfinite-stage-v1

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
noncomputable def decodedGalerkinOperatorDFiniteStage
    (n : ℕ)
    (μ : Fin N → ℝ)
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re (inner ℂ y (decodedGalerkinOpCLM μ δ qs w L M y))) :
    DFiniteStage :=
  { primePowerStage n with
    E := EuclideanSpace ℂ (Fin N)
    instNormed := inferInstance
    instInner := inferInstance
    instComplete := inferInstance
    native := decodedGalerkinNativeStage μ δ qs w L M hnn
    appendixDFiniteFStage := decodedGalerkinPerturbedFStage (N := N) μ δ qs w L }

/--
The real prime-operator stage has the correct F-stage:
not zero, not free, but the prime-perturbed resolvent trace.
-/
theorem decodedGalerkinOperatorDFiniteStage_F_stage
    (n : ℕ)
    (μ : Fin N → ℝ)
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re (inner ℂ y (decodedGalerkinOpCLM μ δ qs w L M y))) :
    (decodedGalerkinOperatorDFiniteStage n μ δ qs w L M hnn).appendixDFiniteFStage =
      decodedGalerkinPerturbedFStage (N := N) μ δ qs w L := by
  rfl

/--
The cutoff is inherited from `primePowerStage`.
-/
theorem decodedGalerkinOperatorDFiniteStage_R
    (n : ℕ)
    (μ : Fin N → ℝ)
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (M : ℝ)
    (hnn :
      ∀ y : EuclideanSpace ℂ (Fin N),
        0 ≤ RCLike.re (inner ℂ y (decodedGalerkinOpCLM μ δ qs w L M y))) :
    (decodedGalerkinOperatorDFiniteStage n μ δ qs w L M hnn).R = (n : ℝ) + 1 := by
  rfl

#print axioms decodedGalerkinOperatorDFiniteStage
#print axioms decodedGalerkinOperatorDFiniteStage_F_stage
#print axioms decodedGalerkinOperatorDFiniteStage_R

end

end RHFormalization
