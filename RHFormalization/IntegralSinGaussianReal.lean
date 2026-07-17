import RHFormalization.IntegralCosGaussianReal
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory
open scoped Real BigOperators

/-!
# O3 brick 4 — full-line Gaussian sine transform vanishes.
∫_ℝ sin(a u) exp(-b u²) = 0, because the integrand is odd (sin odd × Gaussian even).
Together with brick 3, this collapses the phase split to the pure cosine closed form.
-/

theorem integral_sin_mul_gaussian_real (a b : ℝ) :
    (∫ u : ℝ, Real.sin (a * u) * Real.exp (-b * u ^ 2)) = 0 := by
  set f : ℝ → ℝ := fun u => Real.sin (a * u) * Real.exp (-b * u ^ 2) with hf
  -- oddness: f (-u) = - f u
  have hodd : ∀ u : ℝ, f (-u) = - f u := by
    intro u
    simp only [hf]
    rw [show a * -u = -(a * u) by ring, Real.sin_neg,
        show (-u) ^ 2 = u ^ 2 by ring]
    ring
  -- reflection: ∫ f (-x) = ∫ f x
  have hrefl : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := integral_neg_eq_self f volume
  -- ∫ f (-x) = ∫ (- f x) = - ∫ f x
  have hstep : (∫ x : ℝ, f (-x)) = - ∫ x : ℝ, f x := by
    rw [show (fun x : ℝ => f (-x)) = (fun x : ℝ => - f x) from funext hodd]
    rw [integral_neg]
  -- so ∫ f = - ∫ f  ⟹ ∫ f = 0
  rw [hrefl] at hstep
  linarith [hstep]

#print axioms integral_sin_mul_gaussian_real

end RHFormalization
