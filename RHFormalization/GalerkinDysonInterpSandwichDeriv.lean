import RHFormalization.GalerkinDysonInterpDeriv
import RHFormalization.GalerkinDysonInterp
import RHFormalization.GalerkinFreeHeatDeriv
import Mathlib

/-!
# Dyson interpolation derivative, left-oriented perturbed factor.

The earlier raw product-rule derivative was correct but used the right-oriented
perturbed derivative `P*(-(K+V))`. Since `P = exp(u•(-(K+V)))` commutes with
`-(K+V)`, we also have the left-oriented derivative `(-(K+V))*P`.

With that orientation, the matrix-level cancellation is honest:

  (A*K)*P + A*((-(K+V))*P) = A*(-V)*P.

No trace-cyclicity is needed for this cancellation.
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

/-- Perturbed heat derivative in left-multiplication form. -/
theorem hasDerivAt_galerkinPerturbedHeat_left
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => NormedSpace.exp
        (v • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))))
      ((-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))) u := by
  set B : Matrix (Fin N) (Fin N) ℝ :=
    -(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)
  change HasDerivAt
    (fun v : ℝ => NormedSpace.exp (v • B))
    (B * NormedSpace.exp (u • B)) u
  have h := hasDerivAt_exp_smul_const B u
  convert h using 1
  have hc : Commute B (NormedSpace.exp (u • B)) :=
    ((Commute.refl B).smul_right u).exp_right
  exact hc.eq

/-- Honest Dyson interpolation derivative in the `-V` sandwich form. -/
theorem hasDerivAt_dysonInterp_sandwich
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => dysonInterp (N := N) δ qs w L t v)
      (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))) u := by
  have hfree := hasDerivAt_dysonInterp_freeFactor (N := N) L t u
  have hpert := hasDerivAt_galerkinPerturbedHeat_left (N := N) δ qs w L u
  have hmul := hfree.mul hpert
  unfold dysonInterp
  convert hmul using 1
  noncomm_ring

#print axioms hasDerivAt_galerkinPerturbedHeat_left
#print axioms hasDerivAt_dysonInterp_sandwich

end
end RHFormalization
