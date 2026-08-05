import RHFormalization.SinhSqIntegralKit
import RHFormalization.DirichletGreenKernel
import Mathlib

/-!
# GreenSqDiagonalClosed — P2-B2: the squared-Green diagonal in closed form

ROUTE CARD
1. Target: EXACT closed hyperbolic form of `∫₀^L G_L(x,a;κ)² dx` — the
   position-space squared resolvent diagonal. By the mode expansion
   (Parseval over the banked orthogonal sine family, to be wired in P2-B3)
   this equals `(2/L)·Σ sin²((m+1)πa/L)/(κ²+λ_m)²·(L/2)`-normalized —
   i.e. THE combined density−osc profile shape. Its large-L asymptotics
   carry the `e^{−2κa}` continuum structure the seam kernel demands.
2. Raw B on Ω? NO. B−M bare Prop? NO — split-at-a FTC, pure calculus.
3. Consumer: P2-B3 (Parseval identification with the mode sum) and P2-C
   (large-L asymptotics vs seam kernel — the go/no-go).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

open Real

/-- **P2-B2: closed form of the squared-Green diagonal integral.** -/
theorem greenSq_diagonal_closed (κ L a : ℝ)
    (hκ : 0 < κ) (hL : 0 < L) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    (∫ x in (0:ℝ)..L, dirichletGreen L κ x a ^ 2)
      = (Real.sinh (κ * (L - a)) ^ 2
            * (Real.sinh (κ * a) * Real.cosh (κ * a) / κ - a)
          + Real.sinh (κ * a) ^ 2
            * (Real.sinh (κ * (L - a)) * Real.cosh (κ * (L - a)) / κ
                - (L - a)))
        / (2 * (κ * Real.sinh (κ * L)) ^ 2) := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hsinhL_pos : 0 < Real.sinh (κ * L) := by
    have hkl : 0 < κ * L := by positivity
    first
      | exact Real.sinh_pos_iff.mpr hkl
      | exact (Real.sinh_pos _).mpr hkl
      | exact Real.sinh_pos.mpr hkl
      | (rw [Real.sinh_eq]
         have hlt := Real.exp_lt_exp.mpr (neg_lt_self hkl)
         linarith)
  have hsL0 : Real.sinh (κ * L) ≠ 0 := ne_of_gt hsinhL_pos
  have hsplit :
      (∫ x in (0:ℝ)..a, dirichletGreen L κ x a ^ 2)
        + (∫ x in a..L, dirichletGreen L κ x a ^ 2)
      = ∫ x in (0:ℝ)..L, dirichletGreen L κ x a ^ 2 := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · apply Continuous.intervalIntegrable
      unfold dirichletGreen
      fun_prop (disch := positivity)
    · apply Continuous.intervalIntegrable
      unfold dirichletGreen
      fun_prop (disch := positivity)
  rw [← hsplit]
  have hI1 : (∫ x in (0:ℝ)..a, dirichletGreen L κ x a ^ 2)
      = (Real.sinh (κ * (L - a)) / (κ * Real.sinh (κ * L))) ^ 2
        * (sinhSqAntideriv κ a - sinhSqAntideriv κ 0) := by
    rw [intervalIntegral.integral_congr
        (g := fun x => (Real.sinh (κ * (L - a)) / (κ * Real.sinh (κ * L))) ^ 2
          * Real.sinh (κ * x) ^ 2)]
    · rw [intervalIntegral.integral_const_mul, integral_sinh_sq κ 0 a hκ0]
    · intro x hx
      rw [Set.uIcc_of_le ha0] at hx
      unfold dirichletGreen
      simp only []
      rw [min_eq_left hx.2, max_eq_right hx.2]
      ring
  have hI2 : (∫ x in a..L, dirichletGreen L κ x a ^ 2)
      = (Real.sinh (κ * a) / (κ * Real.sinh (κ * L))) ^ 2
        * (sinhSqRevAntideriv κ L L - sinhSqRevAntideriv κ L a) := by
    rw [intervalIntegral.integral_congr
        (g := fun x => (Real.sinh (κ * a) / (κ * Real.sinh (κ * L))) ^ 2
          * Real.sinh (κ * (L - x)) ^ 2)]
    · rw [intervalIntegral.integral_const_mul, integral_sinhRev_sq κ L a L hκ0]
    · intro x hx
      rw [Set.uIcc_of_le haL] at hx
      unfold dirichletGreen
      simp only []
      rw [min_eq_right hx.1, max_eq_left hx.1]
      ring
  rw [hI1, hI2]
  have hA0 : sinhSqAntideriv κ 0 = 0 := by
    unfold sinhSqAntideriv
    simp
  have hBL : sinhSqRevAntideriv κ L L = -L / 2 := by
    unfold sinhSqRevAntideriv
    simp
  rw [hA0, hBL]
  unfold sinhSqAntideriv sinhSqRevAntideriv
  field_simp
  ring

#print axioms greenSq_diagonal_closed

end RHFormalization
