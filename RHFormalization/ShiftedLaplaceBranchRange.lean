import RHFormalization.ShiftedLaplaceBsharedMeromorphic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace RHFormalization

open Complex Real

/-- The principal square root has nonnegative real part: `Re(√w) ≥ 0`. -/
theorem sqrt_re_nonneg (w : ℂ) : 0 ≤ (Complex.sqrt w).re := by
  unfold Complex.sqrt
  have hcast : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]; norm_num
  rw [hcast, Complex.cpow_ofReal_re]
  apply mul_nonneg
  · positivity
  · apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have h := Complex.neg_pi_lt_arg w
      nlinarith [Real.pi_pos]
    · have h := Complex.arg_le_pi w
      nlinarith [Real.pi_pos]

/-- **`φ` has real part ≥ 1/2.** Since `Re(√(z+¼)) ≥ 0`, the shift by `1/2`
gives `Re(φ z) ≥ 1/2`. -/
theorem phi_re_ge_half (z : ℂ) :
    (1/2 : ℝ) ≤ (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ)).re := by
  have h := sqrt_re_nonneg (z + (1/4:ℂ))
  rw [Complex.add_re]
  have h12 : ((1/2:ℂ)).re = (1/2:ℝ) := by simp
  rw [h12]; linarith

/-- **Squaring back: `φ(z) = ρ ⟹ z = polePoint ρ`.** If the branch `φ` maps
`z` to `ρ`, then `z = -ρ(1-ρ)`. Pure algebra from `(√w)² = w`. -/
theorem polePoint_of_phi_eq {z ρ : ℂ}
    (hphi : Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ) = ρ) :
    z = polePoint ρ := by
  have hsqrt : Complex.sqrt (z + (1/4:ℂ)) = ρ - (1/2:ℂ) := by
    linear_combination hphi
  have hsq : z + (1/4:ℂ) = (ρ - (1/2:ℂ))^2 := by
    have hpow : (Complex.sqrt (z + (1/4:ℂ)))^2 = z + (1/4:ℂ) := by
      unfold Complex.sqrt
      exact Complex.cpow_nat_inv_pow _ (by norm_num)
    rw [hsqrt] at hpow
    linear_combination - hpow
  unfold polePoint
  linear_combination hsq

end RHFormalization
