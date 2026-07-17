import Mathlib

/-!
# Keystone base case (a = 0): the Laplace transform of the heat kernel at a=0.

  INT_0^inf (4 pi t)^{-1/2} e^{-b t} dt = 1/(2 sqrt b)   for b > 0.

Route: substitute t = x^2 (integral_comp_rpow_Ioi_of_pos, p=2), the Jacobian
2x cancels the x in (4 pi x^2)^{-1/2}, leaving (1/sqrt pi) ∫ e^{-b x^2}
= (1/sqrt pi)(sqrt(pi/b)/2) = 1/(2 sqrt b) via integral_gaussian_Ioi.
-/

namespace RHFormalization
open Real MeasureTheory Set
open scoped BigOperators

/-- Real base case: ∫ over Ioi 0 of (4 pi t)^{-1/2} e^{-b t} = 1/(2 sqrt b), b > 0. -/
theorem heatKernel_laplace_base_real (b : Real) (hb : 0 < b) :
    (∫ t in Ioi (0:Real),
        (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (-(b * t)))
      = 1 / (2 * Real.sqrt b) := by
  -- backward substitution t = x^2
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun y : Real => (1 / Real.sqrt (4 * Real.pi * y)) * Real.exp (-(b * y)))
    (p := 2) (by norm_num : (0:Real) < 2)
  rw [← hsub]
  -- now goal: ∫ (2 * x^(2-1)) . g(x^2) = 1/(2 sqrt b)
  -- simplify integrand to (1/sqrt pi) * exp(-b x^2) on Ioi 0
  have hintegrand : (∫ x in Ioi (0:Real),
        (2 * x ^ ((2:Real) - 1)) •
          ((1 / Real.sqrt (4 * Real.pi * x ^ (2:Real))) * Real.exp (-(b * x ^ (2:Real)))))
      = ∫ x in Ioi (0:Real), (1 / Real.sqrt Real.pi) * Real.exp (-(b * x^2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := mem_Ioi.mp hx
    simp only [smul_eq_mul]
    have hxsq : x ^ (2:Real) = x^2 := Real.rpow_two x
    rw [hxsq]
    have h21 : x ^ ((2:Real) - 1) = x := by
      rw [show (2:Real) - 1 = 1 by norm_num, Real.rpow_one]
    rw [h21]
    have hsqrt : Real.sqrt (4 * Real.pi * x^2) = 2 * Real.sqrt Real.pi * x := by
      rw [show (4 : Real) * Real.pi * x^2 = (2 * Real.sqrt Real.pi * x)^2 by
        rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring]
      rw [Real.sqrt_sq (by positivity)]
    rw [hsqrt]
    field_simp
  rw [hintegrand]
  -- pull out constant, apply gaussian
  rw [integral_const_mul]
  rw [show (fun x : Real => Real.exp (-(b * x^2))) = (fun x : Real => Real.exp (-b * x^2)) from by
    funext x; ring_nf]
  rw [integral_gaussian_Ioi b]
  -- goal: (1/sqrt pi) * (sqrt(pi/b)/2) = 1/(2 sqrt b)
  have hsp : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
  have hsb : Real.sqrt b > 0 := Real.sqrt_pos.mpr hb
  rw [Real.sqrt_div Real.pi_pos.le b]
  field_simp

end RHFormalization
