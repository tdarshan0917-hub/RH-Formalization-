import RHFormalization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.RCLike.Sqrt

namespace RHFormalization

open Complex

/-- `polePoint ρ + 1/4 = (ρ - 1/2)^2` (pure algebra). -/
theorem polePoint_add_quarter_eq_sq (ρ : ℂ) :
    polePoint ρ + (1/4 : ℂ) = (ρ - (1/2:ℂ)) ^ (2:ℕ) := by
  unfold polePoint
  ring

/-- For a zero with `re ρ > 1/2`: `√(s0 + 1/4) = ρ - 1/2`, hence `φ(s0) = ρ`. -/
theorem sqrt_polePoint_eq_of_re_gt
    {ρ : ℂ} (h : (1/2 : ℝ) < ρ.re) :
    Complex.sqrt (polePoint ρ + (1/4:ℂ)) = ρ - (1/2:ℂ) := by
  rw [polePoint_add_quarter_eq_sq]
  -- Complex.sqrt x = x^(2⁻¹); apply sq_cpow_two_inv with re(ρ-1/2) > 0
  have hre : 0 < (ρ - (1/2:ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    have : ((1:ℂ)/2).re = (1/2 : ℝ) := by norm_num
    rw [this]; linarith
  unfold Complex.sqrt
  exact sq_cpow_two_inv hre

/-- The full branch identity: `φ(s0) = ρ + 1/2's worth`, giving `φ(s0) = ρ`. -/
theorem phi_polePoint_eq_of_re_gt
    {ρ : ℂ} (h : (1/2 : ℝ) < ρ.re) :
    Complex.sqrt (polePoint ρ + (1/4:ℂ)) + (1/2:ℂ) = ρ := by
  rw [sqrt_polePoint_eq_of_re_gt h]; ring

/-- For a zero with `re ρ < 1/2`: `√(s0 + 1/4) = 1/2 - ρ`, hence `φ(s0) = 1 - ρ`. -/
theorem sqrt_polePoint_eq_of_re_lt
    {ρ : ℂ} (h : ρ.re < (1/2 : ℝ)) :
    Complex.sqrt (polePoint ρ + (1/4:ℂ)) = (1/2:ℂ) - ρ := by
  have halg : polePoint ρ + (1/4 : ℂ) = ((1/2:ℂ) - ρ) ^ (2:ℕ) := by
    unfold polePoint; ring
  rw [halg]
  have hre : 0 < ((1/2:ℂ) - ρ).re := by
    simp only [Complex.sub_re]
    have : ((1:ℂ)/2).re = (1/2 : ℝ) := by norm_num
    rw [this]; linarith
  unfold Complex.sqrt
  exact sq_cpow_two_inv hre

theorem phi_polePoint_eq_of_re_lt
    {ρ : ℂ} (h : ρ.re < (1/2 : ℝ)) :
    Complex.sqrt (polePoint ρ + (1/4:ℂ)) + (1/2:ℂ) = 1 - ρ := by
  rw [sqrt_polePoint_eq_of_re_lt h]; ring

end RHFormalization
