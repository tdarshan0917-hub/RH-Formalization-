import Mathlib
set_option autoImplicit false
open MeasureTheory Real Set

/-- Left-tail Gaussian decay: on `Iic (-R)` with `R>0`, the Gaussian
`exp(-b u^2)` is dominated by the exponential `exp(b*R*u)` (which is ≤ the
Gaussian's decay because `u ≤ -R < 0` makes `b*R*u ≤ -b*R^2`), and the latter
integrates in closed form to `exp(-b R^2)/(b R)`. -/
theorem gaussian_Iic_tail_le
    (b R : ℝ) (hb : 0 < b) (hR : 0 < R) :
    ∫ u in Iic (-R), Real.exp (-b * u ^ 2)
      ≤ Real.exp (-(b * R ^ 2)) / (b * R) := by
  have hbR : 0 < b * R := mul_pos hb hR
  -- integrand integrability on Iic (-R)
  have hInt_g : IntegrableOn (fun u => Real.exp (-b * u ^ 2)) (Iic (-R)) volume :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have hInt_e : IntegrableOn (fun u => Real.exp (b * R * u)) (Iic (-R)) volume :=
    integrableOn_exp_mul_Iic hbR (-R)
  -- pointwise domination: exp(-b u^2) ≤ exp(b*R*u) on Iic (-R)
  have hmono : ∫ u in Iic (-R), Real.exp (-b * u ^ 2)
      ≤ ∫ u in Iic (-R), Real.exp (b * R * u) := by
    apply setIntegral_mono_on hInt_g hInt_e measurableSet_Iic
    intro u hu
    rw [mem_Iic] at hu
    rw [Real.exp_le_exp]
    nlinarith [hu, hb, hR,
      mul_nonneg (show (0:ℝ) ≤ -u by linarith) (show (0:ℝ) ≤ -u - R by linarith)]
  -- evaluate the exponential tail in closed form
  have hclosed : ∫ u in Iic (-R), Real.exp (b * R * u)
      = Real.exp (b * R * (-R)) / (b * R) :=
    integral_exp_mul_Iic hbR (-R)
  calc ∫ u in Iic (-R), Real.exp (-b * u ^ 2)
      ≤ ∫ u in Iic (-R), Real.exp (b * R * u) := hmono
    _ = Real.exp (b * R * (-R)) / (b * R) := hclosed
    _ = Real.exp (-(b * R ^ 2)) / (b * R) := by ring_nf
