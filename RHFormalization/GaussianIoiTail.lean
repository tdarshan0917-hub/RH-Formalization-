import RHFormalization.GaussianIicTail
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open MeasureTheory Real Set

/--
Right-tail Gaussian decay.

Reflection `u ↦ -u` converts the integral on `Ioi R` into the already-banked
left-tail integral on `Iic (-R)`.
-/
theorem gaussian_Ioi_tail_le
    (b R : ℝ) (hb : 0 < b) (hR : 0 < R) :
    ∫ u in Ioi R, Real.exp (-b * u ^ 2)
      ≤ Real.exp (-(b * R ^ 2)) / (b * R) := by

  have hreflect :
      (∫ u in Ioi R, Real.exp (-b * u ^ 2))
        =
      ∫ u in Iic (-R), Real.exp (-b * u ^ 2) := by
    have h :=
      integral_comp_neg_Iic
        (-R)
        (fun u : ℝ => Real.exp (-b * u ^ 2))
    simpa only [neg_sq, neg_neg] using h.symm

  rw [hreflect]
  exact gaussian_Iic_tail_le b R hb hR

#print axioms gaussian_Ioi_tail_le

end RHFormalization
