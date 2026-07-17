import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.ShiftedLaplaceRegionFacts
import RHFormalization.ShiftedLaplaceBRegularAtomic
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityClosure
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

theorem shiftedLaplace_kernel_norm_le
    (a : ℝ) (ha : 0 ≤ a) (s : ℂ) (hs : s ∈ shiftedLaplaceAbsConvRegion) :
    ‖shiftedLaplaceHeatKernelC a s‖ ≤ Real.exp (-(a) / 2) := by
  unfold shiftedLaplaceHeatKernelC
  rw [norm_mul, Complex.norm_exp]
  have hre : (1/2 : ℝ) < (Complex.sqrt (s + (1/4:ℂ))).re := hs
  set w := Complex.sqrt (s + (1/4:ℂ)) with hw
  have hnorm_w : (1/2:ℝ) < ‖w‖ := lt_of_lt_of_le hre (Complex.re_le_norm w)
  have hbound1 : ‖(1:ℂ) / (2 * w)‖ ≤ 1 := by
    rw [norm_div, norm_mul, norm_one]
    rw [div_le_one (by rw [Complex.norm_two]; positivity)]
    rw [Complex.norm_two]; linarith
  have hexp : (-(a:ℂ) * w).re ≤ -(a)/2 := by
    rw [Complex.mul_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero]
    nlinarith [hre, ha]
  calc ‖(1:ℂ)/(2*w)‖ * Real.exp ((-(a:ℂ)*w).re)
      ≤ 1 * Real.exp (-(a)/2) := by
        apply mul_le_mul hbound1 (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by norm_num)
    _ = Real.exp (-(a)/2) := by ring

theorem center_nonneg (q : PrimePowerPair) : 0 ≤ q.center := by
  unfold PrimePowerPair.center
  rcases Nat.eq_zero_or_pos q.natValue with h | h
  · simp [h]
  · apply Real.log_nonneg
    exact_mod_cast h

noncomputable def shiftedLaplaceMajorant : PrimePowerPair → ℝ :=
  fun q => ‖q.weightC‖ * Real.exp (-(q.center) / 2)

theorem shiftedLaplace_weighted_norm_le
    (q : PrimePowerPair) (s : ℂ) (hs : s ∈ shiftedLaplaceAbsConvRegion) :
    ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ ≤ shiftedLaplaceMajorant q := by
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact shiftedLaplace_kernel_norm_le q.center (center_nonneg q) s hs

#print axioms shiftedLaplace_weighted_norm_le

end
end RHFormalization
