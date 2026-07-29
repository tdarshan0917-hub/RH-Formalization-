import RHFormalization.ShiftedLaplaceSqrtNonzero
import RHFormalization.OmegaTopology

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check shiftedLaplaceShift
#check mem_Omega_iff_re_pos_or_im_ne_zero
#check Complex.mem_slitPlane_iff
#check Complex.slitPlane_ne_zero

example
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    shiftedLaplaceShift z ∈ Complex.slitPlane := by
  have hz_cases : 0 < z.re ∨ z.im ≠ 0 :=
    (mem_Omega_iff_re_pos_or_im_ne_zero z).mp hzΩ
  rw [Complex.mem_slitPlane_iff]
  rcases hz_cases with hz_re | hz_im
  · left
    have hquarter : (0 : ℝ) < (1 / 4 : ℝ) := by norm_num
    have hpos : 0 < z.re + (1 / 4 : ℝ) := by linarith
    simpa [shiftedLaplaceShift] using hpos
  · right
    simpa [shiftedLaplaceShift] using hz_im

example
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    shiftedLaplaceShift z ≠ 0 := by
  exact Complex.slitPlane_ne_zero
    (by
      have hz_cases : 0 < z.re ∨ z.im ≠ 0 :=
        (mem_Omega_iff_re_pos_or_im_ne_zero z).mp hzΩ
      rw [Complex.mem_slitPlane_iff]
      rcases hz_cases with hz_re | hz_im
      · left
        have hquarter : (0 : ℝ) < (1 / 4 : ℝ) := by norm_num
        have hpos : 0 < z.re + (1 / 4 : ℝ) := by linarith
        simpa [shiftedLaplaceShift] using hpos
      · right
        simpa [shiftedLaplaceShift] using hz_im)

end

end RHFormalization
