import RHFormalization.GalerkinDysonInterpDeriv
import RHFormalization.GalerkinDysonInterp
import Mathlib

/-!
# Dyson interpolation derivative (honest product-rule form).

`d/du [exp((t-u)(-K)) · exp(u(-(K+V)))]
  = exp((t-u)(-K))·K·exp(u(-(K+V))) + exp((t-u)(-K))·exp(u(-(K+V)))·(-(K+V))`.

The naive `-V` sandwich is FALSE (K and exp(u(-(K+V))) do not commute). This is
the true derivative; the K-cancellation happens only AFTER taking the trace
(cyclicity) — that is the next brick, not this one.
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

/-- **Dyson interpolation derivative** (honest product-rule form, both terms kept). -/
theorem hasDerivAt_dysonInterp
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => dysonInterp (N := N) δ qs w L t v)
      (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L))) * (galerkinK (N := N) L)
          * NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
        + NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
          * (NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
             * (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))) u := by
  have hfree := hasDerivAt_dysonInterp_freeFactor (N := N) L t u
  have hpert := hasDerivAt_galerkinPerturbedHeat (N := N) δ qs w L u
  have hmul := hfree.mul hpert
  unfold dysonInterp
  exact hmul

#print axioms hasDerivAt_dysonInterp
