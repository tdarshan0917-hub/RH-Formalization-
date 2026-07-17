-- SENTINEL: DH-v3
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.ResolventTraceHolo
import RHFormalization.BSideHeatKernelLaplaceConnector
import Mathlib

/-!
# Ω-holomorphy of the adaptive defect (defect-gate holo input)

Free side: finite sum of T·(s+1/4+μ)⁻¹, poles at −1/4−μ ≤ −1/4 on the cut.
Window side: finite weightC/window sum of shiftedLaplaceHeatKernelC atoms
(slitPlane construction as in the banked halfplane connector).
This is Montel input #1; with overlap0 (#3 banked) and the banked
Ascoli-from-loc_bdd bridge (#4), only loc_bdd (#2) remains open.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- Per-atom window holomorphy at every point of Ω. -/
theorem shiftedLaplaceHeatKernelC_holomorphicAt_Omega (a : ℝ) {z : ℂ}
    (hz : z ∈ Ω) :
    HolomorphicAtC (fun s => shiftedLaplaceHeatKernelC a s) z := by
  have hslit : z + (1/4 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases eq_or_ne z.im 0 with him | him
    · left
      have hre : 0 < z.re := by
        by_contra hcon
        push_neg at hcon
        exact hz ⟨him, hcon⟩
      have hre14 : (z + (1/4 : ℂ)).re = z.re + 1/4 := by
        simp [Complex.add_re]
      rw [hre14]
      linarith
    · right
      have him14 : (z + (1/4 : ℂ)).im = z.im := by
        simp [Complex.add_im]
      rw [him14]
      exact him
  have hne : (z + (1/4 : ℂ)) ≠ 0 := by
    intro h
    rw [h] at hslit
    simp [Complex.mem_slitPlane_iff] at hslit
  have h_sqrt := shiftedLaplaceSqrt_holomorphicAt_of_shift_mem_slitPlane z hslit
  have h_sqrt_ne := shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero z hne
  exact shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt a z h_sqrt h_sqrt_ne

/-- Per-atom free-side holomorphy: `1/(s+1/4+μ)` at every point of Ω, μ ≥ 0. -/
theorem spikeMode_analyticAt_Omega (μ : ℝ) (hμ : 0 ≤ μ) {z : ℂ}
    (hz : z ∈ Ω) :
    AnalyticAt ℂ (fun s : ℂ => 1 / (s + (1/4 : ℂ) + ((μ : ℝ) : ℂ))) z := by
  have hlam : (0:ℝ) ≤ 1/4 + μ := by linarith
  have hne0 : z + (((1/4 + μ : ℝ)) : ℂ) ≠ 0 :=
    add_real_ne_zero_of_mem_Omega hz hlam
  have hne : z + (1/4 : ℂ) + ((μ : ℝ) : ℂ) ≠ 0 := by
    intro h
    apply hne0
    rw [← h]
    push_cast
    ring
  have hden : AnalyticAt ℂ (fun s : ℂ => s + (1/4 : ℂ) + ((μ : ℝ) : ℂ)) z :=
    (analyticAt_id.add analyticAt_const).add analyticAt_const
  exact analyticAt_const.div hden (by simpa using hne)

/-- **DEFECT HOLO — Montel input #1.** -/
theorem adaptiveGalerkinTransformDefect_holo (c : ℝ) (n : ℕ) :
    HolomorphicOnC (fun s => adaptiveGalerkinTransformDefect c n s) Ω := by
  apply holomorphicOnC_of_forall_holomorphicAtC
  intro z hz
  unfold adaptiveGalerkinTransformDefect adaptiveFreePairedTransform
    decodedOneLetterTransform windowedCanonicalPackage galerkinSpikeTransform
  apply AnalyticAt.sub
  · apply analyticAt_const.mul
    have hshape1 : (fun s : ℂ =>
        ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC * ∑ m : Fin (adaptiveN c n),
            ((galerkinT (N := adaptiveN c n) (adaptiveL c n) q.center m m : ℝ) : ℂ) *
              (1 / (s + (1/4 : ℂ) +
                (((fun m : Fin (adaptiveN c n) =>
                    galerkinLam (adaptiveL c n) (m : ℕ)) m : ℝ) : ℂ))))
        = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            (fun s : ℂ =>
              q.weightC * ∑ m : Fin (adaptiveN c n),
                ((galerkinT (N := adaptiveN c n) (adaptiveL c n) q.center m m : ℝ) : ℂ) *
                  (1 / (s + (1/4 : ℂ) +
                    (((fun m : Fin (adaptiveN c n) =>
                        galerkinLam (adaptiveL c n) (m : ℕ)) m : ℝ) : ℂ)))) := by
      funext s
      rw [Finset.sum_apply]
    rw [hshape1]
    apply Finset.analyticAt_sum
    intro q _
    apply analyticAt_const.mul
    have hshape2 : (fun s : ℂ =>
        ∑ m : Fin (adaptiveN c n),
          ((galerkinT (N := adaptiveN c n) (adaptiveL c n) q.center m m : ℝ) : ℂ) *
            (1 / (s + (1/4 : ℂ) +
              (((fun m : Fin (adaptiveN c n) =>
                  galerkinLam (adaptiveL c n) (m : ℕ)) m : ℝ) : ℂ))))
        = ∑ m : Fin (adaptiveN c n),
            (fun s : ℂ =>
              ((galerkinT (N := adaptiveN c n) (adaptiveL c n) q.center m m : ℝ) : ℂ) *
                (1 / (s + (1/4 : ℂ) +
                  (((fun m : Fin (adaptiveN c n) =>
                      galerkinLam (adaptiveL c n) (m : ℕ)) m : ℝ) : ℂ)))) := by
      funext s
      rw [Finset.sum_apply]
    rw [hshape2]
    apply Finset.analyticAt_sum
    intro m _
    apply analyticAt_const.mul
    exact spikeMode_analyticAt_Omega (galerkinLam (adaptiveL c n) (m : ℕ))
      (by unfold galerkinLam; positivity) hz
  · have hshape3 : (fun s : ℂ =>
        ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC * (((adaptiveL c n - q.center) / (2 * adaptiveL c n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s)
        = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            (fun s : ℂ =>
              q.weightC * (((adaptiveL c n - q.center) / (2 * adaptiveL c n) : ℝ) : ℂ) *
                shiftedLaplaceHeatKernelC q.center s) := by
      funext s
      rw [Finset.sum_apply]
    rw [hshape3]
    apply Finset.analyticAt_sum
    intro q _
    exact (analyticAt_const.mul analyticAt_const).mul
      (shiftedLaplaceHeatKernelC_holomorphicAt_Omega q.center hz)

#print axioms shiftedLaplaceHeatKernelC_holomorphicAt_Omega
#print axioms spikeMode_analyticAt_Omega
#print axioms adaptiveGalerkinTransformDefect_holo

end

end RHFormalization
