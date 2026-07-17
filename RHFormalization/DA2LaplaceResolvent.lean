import RHFormalization.FiniteStageSpectrum
import Mathlib

/-!
# D.A2 (finite-stage): Laplace-resolvent termwise identity (manuscript p163)

(s+λ)⁻¹ = ∫₀^∞ e^{-(s+λ)t} dt  for Re s > 0, λ ≥ 0.

Hinge connecting frequency-side F = ∑(s+λᵢ)⁻¹ to the time-side heat trace
∑ e^{-tλᵢ} that the Galerkin/Duhamel bounds control. (D.A2, p163 line 19.)
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/-- **Termwise Laplace-resolvent identity.** For Re a > 0,
`∫₀^∞ e^{-a t} dt = a⁻¹`. -/
theorem integral_cexp_neg_mul_Ioi {a : ℂ} (ha : 0 < a.re) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (-a * (t:ℂ))) = a⁻¹ := by
  have hneg : (-a).re < 0 := by rw [Complex.neg_re]; linarith
  have h := integral_exp_mul_complex_Ioi (a := -a) hneg 0
  -- h : ∫ x in Ioi 0, exp((-a) * x) = - exp((-a) * 0) / (-a)
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, div_neg] at h
  rw [show (fun t : ℝ => Complex.exp (-a * (t:ℂ)))
        = (fun x : ℝ => Complex.exp ((-a) * (x:ℂ))) from rfl]
  rw [h]
  field_simp

#print axioms integral_cexp_neg_mul_Ioi

/-- D.A2 termwise: `(s+λ)⁻¹ = ∫₀^∞ e^{-(s+λ)t} dt` for Re s > 0, λ ≥ 0. -/
theorem inv_eq_laplace_exp (s : ℂ) (lam : ℝ) (hlam : 0 ≤ lam) (hs : 0 < s.re) :
    (s + (lam : ℂ))⁻¹ = ∫ t in Set.Ioi (0:ℝ), Complex.exp (-(s + (lam : ℂ)) * (t : ℂ)) := by
  have hre : 0 < (s + (lam : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith
  rw [integral_cexp_neg_mul_Ioi hre]

#print axioms inv_eq_laplace_exp

end RHFormalization
