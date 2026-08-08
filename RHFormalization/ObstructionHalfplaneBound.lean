import RHFormalization.CanonicalTailObstructionBridge
import RHFormalization.DMRBTailHalfplaneBound
import RHFormalization.DMRRStageHalfplaneBound
import RHFormalization.GalerkinCanonicalResidualBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-!
# ObstructionHalfplaneBound — the four-sector theorem, half-plane case
compensatorM, BcorrWin, galBTail each n-uniformly bounded on Re s ≥ σ > 0
⇒ canonicalTailObstruction n-uniformly bounded there. Manuscript route.
-/

/-- On `Re s ≥ σ > 0`: `√(σ+1/4) ≤ Re √(s+1/4)`. Proof: `w := √z`
satisfies `w*w = z` (cpow half + half = one), so `(Re w)² ≥ Re z` since
`(Re w)² − (Im w)² = Re z` gives `(Re w)² ≥ Re z`. -/
theorem sqrt_re_ge_on_halfplane (σ : ℝ) (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    Real.sqrt (σ + 1/4) ≤ (Complex.sqrt (s + (1/4:ℂ))).re := by
  set z := s + (1/4:ℂ) with hzdef
  have h14 : ((1/4:ℂ)).re = 1/4 := by norm_num
  have hzre : σ + 1/4 ≤ z.re := by
    rw [hzdef, Complex.add_re, h14]
    linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hzre
    linarith [hσ]
  set w := Complex.sqrt z with hwdef
  have hw2 : w * w = z := by
    rw [hwdef]
    unfold Complex.sqrt
    rw [← Complex.cpow_add _ _ hz0]
    norm_num
  have hre : w.re * w.re - w.im * w.im = z.re := by
    have h := congrArg Complex.re hw2
    rwa [Complex.mul_re] at h
  have h0 : 0 ≤ w.re := sqrt_re_nonneg z
  have hsq : σ + 1/4 ≤ w.re * w.re := by nlinarith [mul_self_nonneg w.im]
  calc Real.sqrt (σ + 1/4) ≤ Real.sqrt (w.re * w.re) := Real.sqrt_le_sqrt hsq
    _ = w.re := Real.sqrt_mul_self h0

/-- **compensatorM is n-uniformly bounded on every half-plane** `Re s ≥ σ > 0`. -/
theorem compensatorM_uniform_bound_on_halfplane (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, σ ≤ s.re → ‖compensatorM n s‖ ≤ C := by
  set a := Real.sqrt (σ + 1/4) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha12 : 1/2 < a := by
    have h := Real.sq_sqrt (show (0:ℝ) ≤ σ + 1/4 by linarith)
    nlinarith [Real.sqrt_nonneg (σ + 1/4)]
  have hC0 : (0:ℝ) < (1/(2*a)) * (1/(a - 1/2)) :=
    mul_pos (one_div_pos.mpr (by linarith)) (one_div_pos.mpr (by linarith))
  refine ⟨(1/(2*a)) * (1/(a - 1/2)), le_of_lt hC0, fun n s hs => ?_⟩
  set w := Complex.sqrt (s + (1/4:ℂ)) with hwdef
  have hwre : a ≤ w.re := sqrt_re_ge_on_halfplane σ hσ hs
  have hwnorm : a ≤ ‖w‖ := le_trans hwre (Complex.re_le_norm w)
  have hR0 : (0:ℝ) ≤ admR n := by
    first
      | exact admR_nonneg n
      | exact le_of_lt (admR_pos n)
      | (unfold admR; positivity)
  have hdenom : a - 1/2 ≤ ‖(1/2:ℂ) - w‖ := by
    have h1 : ((1/2:ℂ) - w).re = 1/2 - w.re := by
      norm_num [Complex.sub_re]
    have h2 : w.re - 1/2 ≤ |((1/2:ℂ) - w).re| := by
      rw [h1, abs_of_nonpos (by linarith)]; linarith
    have h3 : |((1/2:ℂ) - w).re| ≤ ‖(1/2:ℂ) - w‖ := Complex.abs_re_le_norm _
    linarith
  have hexp : ‖Complex.exp (((1/2:ℂ) - w) * ((admR n : ℝ):ℂ))‖ ≤ 1 := by
    have hre : ((((1/2:ℂ) - w) * ((admR n : ℝ):ℂ))).re
        = (1/2 - w.re) * (admR n) := by
      have h12 : ((1/2:ℂ) - w).re = 1/2 - w.re := by
        norm_num [Complex.sub_re]
      rw [Complex.mul_re, h12, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hnorm : ‖Complex.exp (((1/2:ℂ) - w) * ((admR n : ℝ):ℂ))‖
        = Real.exp ((((1/2:ℂ) - w) * ((admR n : ℝ):ℂ)).re) := by
      first
        | exact Complex.norm_exp _
        | exact Complex.abs_exp _
        | simp [Complex.norm_exp]
    rw [hnorm, hre, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hR0
  have hw0 : ‖w‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hwnorm)
  unfold compensatorM
  rw [← hwdef, norm_mul]
  have h1 : ‖(1:ℂ) / (2 * w)‖ ≤ 1/(2*a) := by
    rw [norm_div, norm_one, norm_mul]
    have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h2n]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h2 : ‖Complex.exp (((1/2:ℂ) - w) * ((admR n : ℝ):ℂ)) / ((1/2:ℂ) - w)‖
      ≤ 1/(a - 1/2) := by
    rw [norm_div]
    have hd0 : (0:ℝ) < a - 1/2 := by linarith
    first
      | exact div_le_div₀ zero_le_one hexp hd0 hdenom
      | exact div_le_div zero_le_one hexp hd0 hdenom
      | · have hden0 : (0:ℝ) < ‖(1/2:ℂ) - w‖ := lt_of_lt_of_le hd0 hdenom
          gcongr
          exact hexp
  exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)

/-- **THE FOUR-SECTOR THEOREM, HALF-PLANE CASE**: the tail obstruction is
n-uniformly bounded on every compact of every half-plane `Re s ≥ σ > 0`. -/
theorem canonicalTailObstruction_uniform_bound_on_halfplane
    (σ : ℝ) (hσ : 0 < σ) (K : Set ℂ) (hK : IsCompact K)
    (hKσ : ∀ s ∈ K, σ ≤ s.re) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖canonicalTailObstruction n s‖ ≤ C := by
  have hKΩ : K ⊆ Ω := by
    first
      | exact halfplane_subset_Omega σ hσ K hKσ
      | exact fun s hs => halfplane_subset_Omega σ hσ K hKσ hs
  obtain ⟨Cw, hCw0, hw⟩ := BcorrWin_uniform_bound K hK hKΩ
  obtain ⟨CM, hCM0, hM⟩ := compensatorM_uniform_bound_on_halfplane σ hσ
  obtain ⟨CT, hCT⟩ := canonicalPackageTail_uniform_bound_on_halfplane σ hσ
    spikeT0 spikeT0_pos K hKσ
  refine ⟨Cw + CM + CT, fun n s hs => ?_⟩
  have hsre : 0 < s.re := lt_of_lt_of_le hσ (hKσ s hs)
  have hBW : ‖BcorrWin n s‖ ≤ Cw := by
    first
      | exact hw n s hs
      | · have h := hw n s hs
          have hden : (1:ℝ) ≤ (n : ℝ) + 2 := by
            have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith
          have h2 : Cw / ((n : ℝ) + 2) ≤ Cw := div_le_self hCw0.le hden
          linarith
  have hBT : ‖galBTail n s‖ ≤ CT := by
    have heq : galBTail n s
        = canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n))
            spikeT0 s := by
      first
        | exact galB_tail_eq_canonicalPackageTail n s hsre
        | (unfold galBTail; exact galB_tail_eq_canonicalPackageTail n s hsre)
    rw [heq]
    exact hCT n s hs
  rw [canonicalTailObstruction_eq_Bcorr_sub_Btail n s hsre]
  unfold Bcorr
  calc ‖BcorrWin n s + compensatorM n s - galBTail n s‖
      ≤ ‖BcorrWin n s + compensatorM n s‖ + ‖galBTail n s‖ := norm_sub_le _ _
    _ ≤ (‖BcorrWin n s‖ + ‖compensatorM n s‖) + ‖galBTail n s‖ := by
        have := norm_add_le (BcorrWin n s) (compensatorM n s)
        linarith
    _ ≤ Cw + CM + CT := by
        have h3 := hM n s (hKσ s hs)
        linarith

#print axioms sqrt_re_ge_on_halfplane
#print axioms compensatorM_uniform_bound_on_halfplane
#print axioms canonicalTailObstruction_uniform_bound_on_halfplane

end

end RHFormalization
