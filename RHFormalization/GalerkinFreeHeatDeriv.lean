import RHFormalization.GalerkinMatrices
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib

/-!
# Dyson rung 0: derivative of the free/perturbed Galerkin heat semigroups.

The non-diagonal matrix-exp derivatives, with the full L∞ operator-norm instance
stack (group+space+ring+algebra) activated locally — the missing piece that made
`GalerkinHeatDeriv` sorryAx. Genuine operator `galerkinK`, `galerkinK+galerkinV`.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Free Galerkin heat semigroup `exp(v•(-K))`. -/
noncomputable def galerkinFreeHeat (L : ℝ) (v : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  NormedSpace.exp (v • (-(galerkinK (N := N) L)))

/-- **Dyson rung 0 (free).** `d/dv exp(v•(-K)) = exp(v•(-K))*(-K)`. -/
theorem hasDerivAt_galerkinFreeHeat (L : ℝ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => NormedSpace.exp (v • (-(galerkinK (N := N) L))))
      (NormedSpace.exp (u • (-(galerkinK (N := N) L))) * (-(galerkinK (N := N) L))) u :=
  hasDerivAt_exp_smul_const (-(galerkinK (N := N) L)) u

/-- **Dyson rung 0 (perturbed).** `d/dv exp(v•(-(K+V))) = exp(v•(-(K+V)))*(-(K+V))`.
This is the genuine full operator's heat derivative — the object the Duhamel
expansion differentiates. -/
theorem hasDerivAt_galerkinPerturbedHeat
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => NormedSpace.exp
        (v • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))))
      (NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
        * (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))) u :=
  hasDerivAt_exp_smul_const (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)) u

#print axioms hasDerivAt_galerkinFreeHeat
#print axioms hasDerivAt_galerkinPerturbedHeat

end
end RHFormalization
