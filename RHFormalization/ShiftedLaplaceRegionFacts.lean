import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceBsharedMeromorphic
import RHFormalization.OmegaTopology
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.RCLike.Sqrt

namespace RHFormalization

noncomputable section

open Complex Topology Filter Set

theorem shiftedLaplaceAbsConvRegion_shift_mem_slitPlane
    {s : ℂ} (hs : s ∈ shiftedLaplaceAbsConvRegion) :
    (s + (1/4:ℂ)) ∈ Complex.slitPlane := by
  have hre : (1/2:ℝ) < (Complex.sqrt (s + (1/4:ℂ))).re := hs
  by_contra hcon
  rw [Complex.mem_slitPlane_iff] at hcon
  push_neg at hcon
  obtain ⟨hle, him⟩ := hcon
  have heq : s + (1/4:ℂ) = (((s + (1/4:ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]; exact him
  rw [heq, Complex.re_sqrt_ofReal] at hre
  have hz : Real.sqrt ((s + (1/4:ℂ)).re) = 0 :=
    Real.sqrt_eq_zero_of_nonpos hle
  rw [hz] at hre
  linarith

theorem shiftedLaplaceAbsConvRegion_subset_Omega :
    shiftedLaplaceAbsConvRegion ⊆ Ω := by
  intro s hs
  have hslit := shiftedLaplaceAbsConvRegion_shift_mem_slitPlane hs
  rw [Complex.mem_slitPlane_iff] at hslit
  rw [mem_Omega_iff_re_pos_or_im_ne_zero]
  rcases hslit with hre | him
  · have hreg : (1/2:ℝ) < (Complex.sqrt (s + (1/4:ℂ))).re := hs
    by_cases him0 : s.im = 0
    · left
      have heq : s + (1/4:ℂ) = (((s.re + 1/4 : ℝ)) : ℂ) := by
        apply Complex.ext
        · push_cast; simp
        · rw [Complex.ofReal_im]; simp [him0]
      rw [heq, Complex.re_sqrt_ofReal] at hreg
      have hpos : (0:ℝ) ≤ s.re + 1/4 := by
        by_contra hneg
        push_neg at hneg
        rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hneg)] at hreg
        linarith
      nlinarith [Real.sq_sqrt hpos, hreg, Real.sqrt_nonneg (s.re + 1/4)]
    · right; exact him0
  · right
    simpa using him

theorem shiftedLaplaceAbsConvRegion_nonempty :
    shiftedLaplaceAbsConvRegion.Nonempty := by
  refine ⟨(1:ℂ), ?_⟩
  show (1/2:ℝ) < (Complex.sqrt ((1:ℂ) + (1/4:ℂ))).re
  have h54 : (1:ℂ) + (1/4:ℂ) = ((5/4 : ℝ) : ℂ) := by
    apply Complex.ext
    · push_cast; simp; norm_num
    · rw [Complex.ofReal_im]; simp
  rw [h54, Complex.re_sqrt_ofReal]
  have hhalf : (1/2:ℝ) = Real.sqrt (1/4) := by
    rw [show (1/4:ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hhalf]
  apply Real.sqrt_lt_sqrt <;> norm_num

theorem shiftedLaplaceAbsConvRegion_isOpen :
    IsOpen shiftedLaplaceAbsConvRegion := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hslit := shiftedLaplaceAbsConvRegion_shift_mem_slitPlane hs
  have hz : (0:ℝ) ≤ (s + (1/4:ℂ)).re ∨ (s + (1/4:ℂ)).im ≠ 0 := by
    rw [Complex.mem_slitPlane_iff] at hslit
    exact hslit.imp le_of_lt id
  have hcontsqrt : ContinuousAt Complex.sqrt (s + (1/4:ℂ)) :=
    Complex.continuousAt_sqrt hz
  have hg : ContinuousAt (fun z : ℂ => (Complex.sqrt (z + (1/4:ℂ))).re) s := by
    have h1 : ContinuousAt (fun z : ℂ => z + (1/4:ℂ)) s :=
      (continuous_id.add continuous_const).continuousAt
    have h2 : ContinuousAt (fun z : ℂ => Complex.sqrt (z + (1/4:ℂ))) s :=
      hcontsqrt.comp_of_eq h1 rfl
    exact (Complex.continuous_re.continuousAt).comp h2
  have hgt : (1/2:ℝ) < (Complex.sqrt (s + (1/4:ℂ))).re := hs
  have hopen : IsOpen (Set.Ioi (1/2:ℝ)) := isOpen_Ioi
  have hmem : (Complex.sqrt (s + (1/4:ℂ))).re ∈ Set.Ioi (1/2:ℝ) := hgt
  exact hg (hopen.mem_nhds hmem)

#print axioms shiftedLaplaceAbsConvRegion_shift_mem_slitPlane
#print axioms shiftedLaplaceAbsConvRegion_subset_Omega
#print axioms shiftedLaplaceAbsConvRegion_nonempty
#print axioms shiftedLaplaceAbsConvRegion_isOpen

end

end RHFormalization
