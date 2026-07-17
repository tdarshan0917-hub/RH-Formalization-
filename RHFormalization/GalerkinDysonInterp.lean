import RHFormalization.GalerkinFreeHeatDeriv
import RHFormalization.GalerkinMatrices
import Mathlib

/-!
# Dyson interpolation: `s(u) = exp(-(t-u)K) · exp(-u(K+V))`.

Bridges free heat (u=0: `exp(-tK)`) to full heat (u=t: `exp(-t(K+V))`).
Its u-derivative is the order-1 Duhamel integrand. Built on the now-open
matrix-exp derivatives (GalerkinFreeHeatDeriv).
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

/-- The Dyson interpolation `s(u) = exp(-(t-u)K) · exp(-u(K+V))`. -/
noncomputable def dysonInterp
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
    * NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))

/-- **Endpoint u=0**: `dysonInterp t 0 = exp(-tK)` (free heat). -/
theorem dysonInterp_zero
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    dysonInterp (N := N) δ qs w L t 0
      = NormedSpace.exp (t • (-(galerkinK (N := N) L))) := by
  unfold dysonInterp
  rw [sub_zero, zero_smul, NormedSpace.exp_zero, mul_one]

/-- **Endpoint u=t**: `dysonInterp t t = exp(-t(K+V))` (full heat). -/
theorem dysonInterp_self
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    dysonInterp (N := N) δ qs w L t t
      = NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))) := by
  unfold dysonInterp
  rw [sub_self, zero_smul, NormedSpace.exp_zero, one_mul]

#print axioms dysonInterp
#print axioms dysonInterp_zero
#print axioms dysonInterp_self

end
end RHFormalization
