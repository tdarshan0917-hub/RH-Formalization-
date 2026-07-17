import RHFormalization.ShiftedLaplacePatchMTest

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter ComplexOrder

def patchOpen (sigma0 : ℝ) : Set ℂ :=
  {s : ℂ | sigma0 < (Complex.sqrt (s + (1/4:ℂ))).re}

theorem patchOpen_shift_mem_slitPlane {sigma0 : ℝ} (hsig0 : 0 < sigma0)
    {s : ℂ} (hs : s ∈ patchOpen sigma0) :
    (s + (1/4:ℂ)) ∈ Complex.slitPlane := by
  have hre : sigma0 < (Complex.sqrt (s + (1/4:ℂ))).re := hs
  by_contra hcon
  rw [Complex.mem_slitPlane_iff] at hcon
  push_neg at hcon
  obtain ⟨hle, him⟩ := hcon
  have heq : s + (1/4:ℂ) = (((s + (1/4:ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]; exact him
  rw [heq, Complex.re_sqrt_ofReal] at hre
  rw [Real.sqrt_eq_zero_of_nonpos hle] at hre
  linarith

theorem patchOpen_isOpen (sigma0 : ℝ) (hsig0 : 0 < sigma0) :
    IsOpen (patchOpen sigma0) := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hslit := patchOpen_shift_mem_slitPlane hsig0 hs
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
  have hgt : sigma0 < (Complex.sqrt (s + (1/4:ℂ))).re := hs
  exact hg ((isOpen_Ioi).mem_nhds hgt)

noncomputable def patchMTestDataOpen (sigma0 : ℝ) (hsig : (1:ℝ)/2 < sigma0) :
    ShiftedLaplaceOnePatchMTestData (patchOpen sigma0) :=
{ u := patchMajorant sigma0
  h_summable := patchMajorant_summable sigma0 hsig
  h_bound := by
    intro q s hs
    have hsq : sigma0 ≤ (Complex.sqrt (s + (1/4:ℂ))).re := le_of_lt hs
    rw [norm_mul]
    calc ‖q.weightC‖ * ‖shiftedLaplaceHeatKernelC q.center s‖
        ≤ ‖q.weightC‖ * ((1/(2*sigma0)) * Real.exp (-(q.center) * sigma0)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact shiftedLaplace_kernel_norm_le_of_re_ge q.center (center_nonneg q)
            sigma0 (by linarith) s hsq
      _ = patchMajorant sigma0 q := by unfold patchMajorant; ring }

noncomputable def patchLevel (z : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion}) : ℝ :=
  ((Complex.sqrt (z.1 + (1/4:ℂ))).re + 1/2) / 2

theorem patchLevel_gt_half (z : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion}) :
    (1:ℝ)/2 < patchLevel z := by
  have hz : (1/2:ℝ) < (Complex.sqrt (z.1 + (1/4:ℂ))).re := z.2
  unfold patchLevel; linarith

theorem patchLevel_pos (z : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion}) :
    0 < patchLevel z := by have := patchLevel_gt_half z; linarith

theorem patchLevel_lt (z : {z : ℂ // z ∈ shiftedLaplaceAbsConvRegion}) :
    patchLevel z < (Complex.sqrt (z.1 + (1/4:ℂ))).re := by
  have hz : (1/2:ℝ) < (Complex.sqrt (z.1 + (1/4:ℂ))).re := z.2
  unfold patchLevel; linarith

noncomputable def shiftedLaplaceLocalMTest : ShiftedLaplaceAbsConvLocalMTestData :=
{ U := fun z => patchOpen (patchLevel z)
  hU_open := fun z => patchOpen_isOpen (patchLevel z) (patchLevel_pos z)
  hU_cover := by
    intro s hs
    refine Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩
    show patchLevel ⟨s, hs⟩ < (Complex.sqrt (s + (1/4:ℂ))).re
    exact patchLevel_lt ⟨s, hs⟩
  patch := fun z => patchMTestDataOpen (patchLevel z) (patchLevel_gt_half z) }

#print axioms shiftedLaplaceLocalMTest

end
end RHFormalization
