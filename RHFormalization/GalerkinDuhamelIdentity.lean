import RHFormalization.GalerkinDysonInterpSandwichDeriv
import RHFormalization.GalerkinDysonInterp
import Mathlib

/-!
# Order-1 Duhamel identity (FTC on the Dyson interpolation).

Since `dysonInterp` goes from `exp(-tK)` (u=0) to `exp(-t(K+V))` (u=t) with
derivative the `-V` sandwich, FTC-2 gives:

  exp(-t(K+V)) - exp(-tK) = ∫₀ᵗ exp((t-u)(-K))·(-V)·exp(u(-(K+V))) du.
-/

set_option autoImplicit false
namespace RHFormalization
noncomputable section
open Matrix MeasureTheory intervalIntegral
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- **Order-1 Duhamel identity.** `exp(-t(K+V)) - exp(-tK) = ∫₀ᵗ (-V sandwich) du`. -/
theorem galerkinDuhamel_identity
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
      - NormedSpace.exp (t • (-(galerkinK (N := N) L)))
      = ∫ u in (0:ℝ)..t,
          NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))) := by
  -- FTC-2: ∫₀ᵗ (deriv) = interp(t) - interp(0)
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) t,
      HasDerivAt (fun v : ℝ => dysonInterp (N := N) δ qs w L t v)
        (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) δ qs w L))
          * NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))) u :=
    fun u _ => hasDerivAt_dysonInterp_sandwich (N := N) δ qs w L t u
  have hcont : ContinuousOn
      (fun u : ℝ => NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))))
      (Set.uIcc 0 t) := by
    apply Continuous.continuousOn
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  rw [dysonInterp_self, dysonInterp_zero]

#print axioms galerkinDuhamel_identity
