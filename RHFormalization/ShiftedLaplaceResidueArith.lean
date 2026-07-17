import RHFormalization.ShiftedLaplacePhiDeriv
import RHFormalization.ShiftedLaplaceBranchIdentity
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

namespace RHFormalization

open Complex

/-- Bridge: `(s+1/4)^(-1/2) = (Complex.sqrt (s+1/4))⁻¹`. -/
theorem cpow_neg_half_eq_inv_sqrt (s : ℂ) :
    (s + (1/4:ℂ)) ^ (-1/2 : ℂ) = (Complex.sqrt (s + (1/4:ℂ)))⁻¹ := by
  have h1 : (-1/2 : ℂ) = -(2⁻¹ : ℂ) := by norm_num
  rw [h1, cpow_neg]
  rfl

/-- `ρ - 1/2 ≠ 0` when `re ρ > 1/2`. -/
theorem sub_half_ne_zero_of_re_gt {ρ : ℂ} (h : (1/2:ℝ) < ρ.re) :
    ρ - (1/2:ℂ) ≠ 0 := by
  intro hz
  have hre : (ρ - (1/2:ℂ)).re = 0 := by rw [hz]; simp
  simp only [Complex.sub_re] at hre
  have : ((1:ℂ)/2).re = (1/2:ℝ) := by norm_num
  rw [this] at hre
  linarith

/-- **The key cancellation** (case `re ρ > 1/2`): the prefactor divided by `φ'(s0)`
equals `-1`. The `(ρ - 1/2)` factors cancel exactly. -/
theorem prefactor_div_phiDeriv_eq_neg_one_of_re_gt
    {ρ : ℂ} (h : (1/2:ℝ) < ρ.re) (hΩ : polePoint ρ ∈ Ω) :
    (-(1 / (2 * Complex.sqrt (polePoint ρ + (1/4:ℂ)))))
        / deriv shiftedPhi (polePoint ρ) = -1 := by
  -- φ'(s0) = (s0+1/4)^(-1/2)/2 = (sqrt(s0+1/4))⁻¹/2
  rw [shiftedPhi_deriv_of_mem_Omega hΩ, cpow_neg_half_eq_inv_sqrt]
  -- sqrt(s0+1/4) = ρ - 1/2
  rw [sqrt_polePoint_eq_of_re_gt h]
  -- now: -(1/(2*(ρ-1/2))) / ((ρ-1/2)⁻¹/2) = -1
  have hne : ρ - (1/2:ℂ) ≠ 0 := sub_half_ne_zero_of_re_gt h
  have hden : ((ρ - (1/2:ℂ))⁻¹ / 2) ≠ 0 := div_ne_zero (inv_ne_zero hne) (by norm_num)
  rw [div_eq_iff hden]
  field_simp

/-- `1/2 - ρ ≠ 0` when `re ρ < 1/2`. -/
theorem half_sub_ne_zero_of_re_lt {ρ : ℂ} (h : ρ.re < (1/2:ℝ)) :
    (1/2:ℂ) - ρ ≠ 0 := by
  intro hz
  have hre : ((1/2:ℂ) - ρ).re = 0 := by rw [hz]; simp
  simp only [Complex.sub_re] at hre
  have : ((1:ℂ)/2).re = (1/2:ℝ) := by norm_num
  rw [this] at hre
  linarith

/-- **The key cancellation** (case `re ρ < 1/2`): prefactor / φ'(s0) = -1. -/
theorem prefactor_div_phiDeriv_eq_neg_one_of_re_lt
    {ρ : ℂ} (h : ρ.re < (1/2:ℝ)) (hΩ : polePoint ρ ∈ Ω) :
    (-(1 / (2 * Complex.sqrt (polePoint ρ + (1/4:ℂ)))))
        / deriv shiftedPhi (polePoint ρ) = -1 := by
  rw [shiftedPhi_deriv_of_mem_Omega hΩ, cpow_neg_half_eq_inv_sqrt]
  rw [sqrt_polePoint_eq_of_re_lt h]
  have hne : (1/2:ℂ) - ρ ≠ 0 := half_sub_ne_zero_of_re_lt h
  have hden : (((1/2:ℂ) - ρ)⁻¹ / 2) ≠ 0 := div_ne_zero (inv_ne_zero hne) (by norm_num)
  rw [div_eq_iff hden]
  field_simp


end RHFormalization
