import RHFormalization.RiemannSliceError
import Mathlib

/-!
# Cosine-Gaussian derivative bound — G3-ii-b sub-brick 2
SENTINEL: cos-gauss-deriv-v1

ROUTE CARD
1. `cosGauss` = e^{−tξ²}cos(ξa), the comparison integrand;
   `cosGaussDeriv` = its exact derivative.
2. `cosGauss_hasDerivAt`: the derivative fact (chain + product rule).
3. `abs_cosGaussDeriv_le`: |f'(ξ)| ≤ (2t·ξ + |a|)·e^{−tξ²} for ξ ≥ 0 —
   the closed majorant the slice engine consumes.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The comparison integrand `e^{−tξ²}·cos(ξa)`. -/
def cosGauss (t a ξ : ℝ) : ℝ :=
  Real.exp (-(t * ξ ^ 2)) * Real.cos (ξ * a)

/-- Its exact derivative. -/
def cosGaussDeriv (t a ξ : ℝ) : ℝ :=
  (-(2 * t * ξ)) * Real.exp (-(t * ξ ^ 2)) * Real.cos (ξ * a)
    - a * Real.exp (-(t * ξ ^ 2)) * Real.sin (ξ * a)

/-- The derivative fact. -/
theorem cosGauss_hasDerivAt (t a ξ : ℝ) :
    HasDerivAt (cosGauss t a) (cosGaussDeriv t a ξ) ξ := by
  unfold cosGauss cosGaussDeriv
  have hpoly : HasDerivAt (fun x : ℝ => -(t * x ^ 2)) (-(2 * t * ξ)) ξ := by
    have h := ((hasDerivAt_pow 2 ξ).const_mul t).neg
    convert h using 1
    push_cast
    ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(t * x ^ 2)))
      ((-(2 * t * ξ)) * Real.exp (-(t * ξ ^ 2))) ξ := by
    have h := hpoly.exp
    convert h using 1
    ring
  have hlin : HasDerivAt (fun x : ℝ => x * a) a ξ := by
    simpa using (hasDerivAt_id ξ).mul_const a
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (x * a))
      (-Real.sin (ξ * a) * a) ξ := by
    have h := hlin.cos
    convert h using 1
  have hprod := hexp.mul hcos
  convert hprod using 1
  ring

/-- **The closed majorant**: `|f'| ≤ (2t·ξ + |a|)·e^{−tξ²}` for `t, ξ ≥ 0`. -/
theorem abs_cosGaussDeriv_le (t a ξ : ℝ) (ht : 0 ≤ t) (hξ : 0 ≤ ξ) :
    |cosGaussDeriv t a ξ| ≤ (2 * t * ξ + |a|) * Real.exp (-(t * ξ ^ 2)) := by
  unfold cosGaussDeriv
  have hE : (0 : ℝ) < Real.exp (-(t * ξ ^ 2)) := Real.exp_pos _
  have hcos : |Real.cos (ξ * a)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hsin : |Real.sin (ξ * a)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc |(-(2 * t * ξ)) * Real.exp (-(t * ξ ^ 2)) * Real.cos (ξ * a)
        - a * Real.exp (-(t * ξ ^ 2)) * Real.sin (ξ * a)|
      ≤ |(-(2 * t * ξ)) * Real.exp (-(t * ξ ^ 2)) * Real.cos (ξ * a)|
          + |a * Real.exp (-(t * ξ ^ 2)) * Real.sin (ξ * a)| :=
        abs_sub _ _
    _ ≤ (2 * t * ξ) * Real.exp (-(t * ξ ^ 2))
          + |a| * Real.exp (-(t * ξ ^ 2)) := by
        apply add_le_add
        · rw [abs_mul, abs_mul, abs_neg]
          have h1 : |2 * t * ξ| = 2 * t * ξ := abs_of_nonneg (by positivity)
          rw [h1, abs_of_pos hE]
          calc 2 * t * ξ * Real.exp (-(t * ξ ^ 2)) * |Real.cos (ξ * a)|
              ≤ 2 * t * ξ * Real.exp (-(t * ξ ^ 2)) * 1 := by
                apply mul_le_mul_of_nonneg_left hcos
                positivity
            _ = 2 * t * ξ * Real.exp (-(t * ξ ^ 2)) := by ring
        · rw [abs_mul, abs_mul, abs_of_pos hE]
          calc |a| * Real.exp (-(t * ξ ^ 2)) * |Real.sin (ξ * a)|
              ≤ |a| * Real.exp (-(t * ξ ^ 2)) * 1 := by
                apply mul_le_mul_of_nonneg_left hsin
                positivity
            _ = |a| * Real.exp (-(t * ξ ^ 2)) := by ring
    _ = (2 * t * ξ + |a|) * Real.exp (-(t * ξ ^ 2)) := by ring

/-- Continuity of the derivative (needed by the slice engine). -/
theorem cosGaussDeriv_continuous (t a : ℝ) :
    Continuous (cosGaussDeriv t a) := by
  unfold cosGaussDeriv
  continuity

#print axioms cosGauss_hasDerivAt
#print axioms abs_cosGaussDeriv_le
#print axioms cosGaussDeriv_continuous

end

end RHFormalization
