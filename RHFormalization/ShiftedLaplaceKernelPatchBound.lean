import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.ShiftedLaplaceRegionFacts
import RHFormalization.ShiftedLaplaceBRegularAtomic
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

theorem shiftedLaplace_kernel_norm_le_of_re_ge
    (a : ℝ) (ha : 0 ≤ a) (sigma : ℝ) (hsig : 0 < sigma) (s : ℂ)
    (hs : sigma ≤ (Complex.sqrt (s + (1/4:ℂ))).re) :
    ‖shiftedLaplaceHeatKernelC a s‖ ≤ (1/(2*sigma)) * Real.exp (-(a) * sigma) := by
  unfold shiftedLaplaceHeatKernelC
  rw [norm_mul, Complex.norm_exp]
  set w := Complex.sqrt (s + (1/4:ℂ)) with hw
  have hwre_pos : (0:ℝ) < w.re := lt_of_lt_of_le hsig hs
  have hnorm_w : sigma ≤ ‖w‖ := le_trans hs (Complex.re_le_norm w)
  have hnorm_pos : (0:ℝ) < ‖w‖ := lt_of_lt_of_le hsig hnorm_w
  have hbound1 : ‖(1:ℂ) / (2 * w)‖ ≤ 1/(2*sigma) := by
    rw [norm_div, norm_mul, norm_one, Complex.norm_two]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hexp : (-(a:ℂ) * w).re ≤ -(a) * sigma := by
    rw [Complex.mul_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero]
    nlinarith [hs, ha, hsig]
  calc ‖(1:ℂ)/(2*w)‖ * Real.exp ((-(a:ℂ)*w).re)
      ≤ (1/(2*sigma)) * Real.exp (-(a)*sigma) := by
        apply mul_le_mul hbound1 (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
        positivity
    _ = (1/(2*sigma)) * Real.exp (-(a)*sigma) := by ring

#print axioms shiftedLaplace_kernel_norm_le_of_re_ge

end
end RHFormalization
