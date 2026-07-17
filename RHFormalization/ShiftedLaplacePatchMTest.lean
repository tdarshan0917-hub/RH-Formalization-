import RHFormalization.ShiftedLaplaceKernelPatchBound
import RHFormalization.ShiftedLaplacePrimeSummable
import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.ShiftedLaplaceMajorant
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter ComplexOrder

def patchAt (sigma0 : ℝ) : Set ℂ :=
  {s : ℂ | sigma0 ≤ (Complex.sqrt (s + (1/4:ℂ))).re}

noncomputable def patchMajorant (sigma0 : ℝ) : PrimePowerPair → ℝ :=
  fun q => ‖q.weightC‖ * ((1/(2*sigma0)) * Real.exp (-(q.center) * sigma0))

theorem patchMajorant_summable (sigma0 : ℝ) (hsig : (1:ℝ)/2 < sigma0) :
    Summable (patchMajorant sigma0) := by
  have hsig_pos : (0:ℝ) < sigma0 := by linarith
  set s0 : ℂ := ((sigma0^2 - 1/4 : ℝ) : ℂ) with hs0
  have heq : s0 + (1/4:ℂ) = (((sigma0^2 : ℝ)) : ℂ) := by
    rw [hs0]; push_cast; ring
  have hnn : (0:ℂ) ≤ s0 + (1/4:ℂ) := by
    rw [heq]; exact Complex.zero_le_real.mpr (by positivity)
  have hsqrt : Complex.sqrt (s0 + (1/4:ℂ)) = (((sigma0 : ℝ)) : ℂ) := by
    rw [Complex.sqrt_of_nonneg hnn, heq, Complex.ofReal_re,
      show (sigma0^2 : ℝ) = sigma0 * sigma0 by ring,
      Real.sqrt_mul_self (le_of_lt hsig_pos)]
  have hre : (Complex.sqrt (s0 + (1/4:ℂ))).re = sigma0 := by
    rw [hsqrt, Complex.ofReal_re]
  have hnorm : ‖2 * Complex.sqrt (s0 + (1/4:ℂ))‖ = 2 * sigma0 := by
    rw [hsqrt, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsig_pos]
  have hs0_region : (1:ℝ)/2 < (Complex.sqrt (s0 + (1/4:ℂ))).re := by rw [hre]; exact hsig
  have hbank := laplace_norm_summable_full (s := s0) hs0_region
  have hpt : ∀ q : PrimePowerPair,
      ‖q.weightC * shiftedLaplaceHeatKernelC q.center s0‖ = patchMajorant sigma0 q := by
    intro q
    rw [norm_mul, norm_shiftedLaplaceHeatKernelC, hnorm, hre]
    unfold patchMajorant; ring
  have hfun : (fun q => ‖q.weightC * shiftedLaplaceHeatKernelC q.center s0‖)
        = patchMajorant sigma0 := funext hpt
  rwa [hfun] at hbank

noncomputable def patchMTestData (sigma0 : ℝ) (hsig : (1:ℝ)/2 < sigma0) :
    ShiftedLaplaceOnePatchMTestData (patchAt sigma0) :=
{ u := patchMajorant sigma0
  h_summable := patchMajorant_summable sigma0 hsig
  h_bound := by
    intro q s hs
    have hsq : sigma0 ≤ (Complex.sqrt (s + (1/4:ℂ))).re := hs
    rw [norm_mul]
    calc ‖q.weightC‖ * ‖shiftedLaplaceHeatKernelC q.center s‖
        ≤ ‖q.weightC‖ * ((1/(2*sigma0)) * Real.exp (-(q.center) * sigma0)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact shiftedLaplace_kernel_norm_le_of_re_ge q.center (center_nonneg q)
            sigma0 (by linarith) s hsq
      _ = patchMajorant sigma0 q := by unfold patchMajorant; ring }

#print axioms patchMTestData

end
end RHFormalization
