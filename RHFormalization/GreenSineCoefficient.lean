import RHFormalization.SinhSinAntiderivKit
import RHFormalization.DirichletGreenKernel
import Mathlib

/-!
# GreenSineCoefficient — P2-A2: the Green kernel IS the resolvent, mode-by-mode

ROUTE CARD
1. Target: for `0 ≤ y ≤ L`, `κ > 0`, `sin(bL) = 0`, `κ²+b² ≠ 0`:
   `∫₀^L dirichletGreen L κ x y · sin(bx) dx = sin(by)/(κ²+b²)`
   — the sine coefficient of the Green kernel is the resolvent value at
   the mode. This JOINS the two D.LOC-1 stones (closed hyperbolic kernel ↔
   spectral modes) and is the spectral-expansion engine for the Phase-2
   combined density−osc continuum match. Symbolically verified exact
   (b-terms cancel via sinh addition; sin(bL)=0 kills only the L-boundary).
2. Raw B on Ω? NO. B−M bare Prop? NO — split-at-y FTC + hyperbolic algebra.
3. Consumer: squared-Green mode expansion (∂κ² route) → combined-profile
   continuum match (the go/no-go theorem).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

open Real

/-- **P2-A2: the Green sine coefficient.** -/
theorem green_sine_coefficient (κ b L y : ℝ)
    (hκ : 0 < κ) (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L)
    (hden : κ^2 + b^2 ≠ 0) (hsinbL : Real.sin (b * L) = 0) :
    (∫ x in (0:ℝ)..L, dirichletGreen L κ x y * Real.sin (b * x))
      = Real.sin (b * y) / (κ^2 + b^2) := by
  have hsinhL_pos : 0 < Real.sinh (κ * L) := by
    have hkl : 0 < κ * L := by positivity
    first
      | exact Real.sinh_pos_iff.mpr hkl
      | exact (Real.sinh_pos _).mpr hkl
      | exact Real.sinh_pos.mpr hkl
      | (rw [Real.sinh_eq]
         have hlt := Real.exp_lt_exp.mpr (neg_lt_self hkl)
         linarith)
  have hsplit :
      (∫ x in (0:ℝ)..y, dirichletGreen L κ x y * Real.sin (b * x))
        + (∫ x in y..L, dirichletGreen L κ x y * Real.sin (b * x))
      = ∫ x in (0:ℝ)..L, dirichletGreen L κ x y * Real.sin (b * x) := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · apply Continuous.intervalIntegrable
      unfold dirichletGreen
      fun_prop (disch := positivity)
    · apply Continuous.intervalIntegrable
      unfold dirichletGreen
      fun_prop (disch := positivity)
  rw [← hsplit]
  -- Left piece: x ≤ y so min = x, max = y
  have hI1 : (∫ x in (0:ℝ)..y, dirichletGreen L κ x y * Real.sin (b * x))
      = (Real.sinh (κ * (L - y)) / (κ * Real.sinh (κ * L)))
        * (sinhSinAntideriv κ b y - sinhSinAntideriv κ b 0) := by
    rw [intervalIntegral.integral_congr
        (g := fun x => (Real.sinh (κ * (L - y)) / (κ * Real.sinh (κ * L)))
          * (Real.sinh (κ * x) * Real.sin (b * x)))]
    · rw [intervalIntegral.integral_const_mul,
        integral_sinh_mul_sin κ b 0 y hden]
    · intro x hx
      rw [Set.uIcc_of_le hy0] at hx
      unfold dirichletGreen
      simp only []
      rw [min_eq_left hx.2, max_eq_right hx.2]
      ring
  -- Right piece: y ≤ x so min = y, max = x
  have hI2 : (∫ x in y..L, dirichletGreen L κ x y * Real.sin (b * x))
      = (Real.sinh (κ * y) / (κ * Real.sinh (κ * L)))
        * (sinhSinRevAntideriv κ b L L - sinhSinRevAntideriv κ b L y) := by
    rw [intervalIntegral.integral_congr
        (g := fun x => (Real.sinh (κ * y) / (κ * Real.sinh (κ * L)))
          * (Real.sinh (κ * (L - x)) * Real.sin (b * x)))]
    · rw [intervalIntegral.integral_const_mul,
        integral_sinhRev_mul_sin κ b L y L hden]
    · intro x hx
      rw [Set.uIcc_of_le hyL] at hx
      unfold dirichletGreen
      simp only []
      rw [min_eq_right hx.1, max_eq_left hx.1]
      ring
  rw [hI1, hI2]
  -- endpoint evaluations
  have hA0 : sinhSinAntideriv κ b 0 = 0 := by
    unfold sinhSinAntideriv
    simp
  have hBL : sinhSinRevAntideriv κ b L L = 0 := by
    unfold sinhSinRevAntideriv
    simp [hsinbL]
  rw [hA0, hBL]
  -- the hyperbolic collapse
  have haddition : Real.sinh (κ * L)
      = Real.sinh (κ * y) * Real.cosh (κ * (L - y))
        + Real.cosh (κ * y) * Real.sinh (κ * (L - y)) := by
    rw [show κ * L = κ * y + κ * (L - y) by ring, Real.sinh_add]
  unfold sinhSinAntideriv sinhSinRevAntideriv
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hsL0 : Real.sinh (κ * L) ≠ 0 := ne_of_gt hsinhL_pos
  field_simp
  first
    | linear_combination
        (κ * Real.sin (b * y)) * haddition
    | linear_combination
        (κ * Real.sin (b * y) * (κ^2 + b^2)) * haddition
    | (rw [haddition]; ring)
    | linear_combination
        (Real.sin (b * y) * κ * (κ^2 + b^2) * Real.sinh (κ * L)) * haddition
    | nlinarith [haddition, sq_nonneg κ, sq_nonneg b]

#print axioms green_sine_coefficient

end RHFormalization
