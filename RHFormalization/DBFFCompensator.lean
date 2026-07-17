import RHFormalization.DBFFDeficitVanishing
import RHFormalization.ResolventTraceHolo
import RHFormalization.ShiftedLaplaceSqrtReLowerBound
import RHFormalization.ShiftedLaplaceOmegaGeometry
import RHFormalization.MontelUniqueLimit

/-!
# DBFFCompensator — Lemma D.OP.1 (main-term compensator M_α)

ROUTE CARD
1. Target: component of the `Bcorr` slot of `DBFFCorrectedBulkProvider`.
   M_α meets the slot's two requirements: Ω-holomorphy (next file);
   → 0 pointwise on RHP(1) (this file).
2. Object: M_α(s) = (2w)⁻¹·exp((1/2−w)·admR n)/(1/2−w), w = √(s+1/4).
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright.
6. Manuscript: D.OP-BOUND, Lemma D.OP.1. 7. Consumer: Bcorr assembly (O1–O3).
Pin facts: Ω is notation for Omega (never unfold Ω); use mem_Omega_iff.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology

/-- The main-term compensator. -/
def compensatorM (n : ℕ) (s : ℂ) : ℂ :=
  (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) *
    (Complex.exp (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * (admR n : ℝ)) /
      ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))))

/-- Zero is on the cut. -/
theorem zero_not_mem_Omega : (0:ℂ) ∉ Ω := by
  intro h0
  have h : (0:ℂ) + ((0:ℝ):ℂ) ≠ 0 := add_real_ne_zero_of_mem_Omega h0 le_rfl
  exact h (by simp)

/-- On Ω, `√(s+1/4) ≠ 1/2` (else `s = 0`, on the cut). -/
theorem sqrt_ne_half {s : ℂ} (hs : s ∈ Ω) :
    Complex.sqrt (s + (1/4:ℂ)) ≠ (1/2:ℂ) := by
  intro h
  have hsq : (Complex.sqrt (s + (1/4:ℂ)))^2 = s + (1/4:ℂ) := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow _ (by norm_num)
  have hs0 : s = 0 := by
    have h1 : ((1/2:ℂ))^2 = s + (1/4:ℂ) := by rw [← h, hsq]
    have h2 : (1/4:ℂ) = s + (1/4:ℂ) := by rw [← h1]; norm_num
    linear_combination -h2
  exact zero_not_mem_Omega (hs0 ▸ hs)

/-- On Ω, `√(s+1/4) ≠ 0`. -/
theorem sqrt_ne_zero' {s : ℂ} (hs : s ∈ Ω) :
    Complex.sqrt (s + (1/4:ℂ)) ≠ 0 := by
  intro h0
  have hsq : (Complex.sqrt (s + (1/4:ℂ)))^2 = s + (1/4:ℂ) := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow _ (by norm_num)
  have hne := shiftedLaplaceShift_ne_zero_of_mem_Omega s hs
  apply hne
  have hunf : shiftedLaplaceShift s = s + (1/4:ℂ) := by
    rfl
  rw [hunf, ← hsq, h0]
  ring

/-- **D.OP.1(ii)**: the compensator vanishes pointwise on RHP(1). -/
theorem compensatorM_overlap0 {s : ℂ}
    (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto (fun n : ℕ => compensatorM n s) atTop (𝓝 (0:ℂ)) := by
  have hre : (1/2:ℝ) < (Complex.sqrt (s + (1/4:ℂ))).re :=
    rightHalfPlane_one_subset_shiftedLaplaceAbsConvRegion hs
  set w := Complex.sqrt (s + (1/4:ℂ)) with hw
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ n : ℕ, ‖compensatorM n s‖
      = (‖(1:ℂ) / ((2:ℂ)*w)‖ / ‖(1/2:ℂ) - w‖) *
        Real.exp (((1/2:ℝ) - w.re) * admR n) := by
    intro n
    unfold compensatorM
    rw [← hw]
    rw [norm_mul, norm_div, norm_div, Complex.norm_exp]
    try simp only [← hw]
    have h12 : ((1/2:ℂ)) = (((1/2:ℝ)):ℂ) := by
      first
        | (norm_num; done)
        | (push_cast; ring)
        | (simp; done)
    have hre2 : ((((1/2:ℂ) - w) * ((admR n : ℝ) : ℂ)).re)
        = ((1/2:ℝ) - w.re) * admR n := by
      first
        | (rw [h12, Complex.mul_re]
           simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
           done)
        | (rw [Complex.mul_re]
           simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
           done)
        | (rw [h12]
           simp [Complex.mul_re, Complex.sub_re, Complex.sub_im,
                 Complex.ofReal_re, Complex.ofReal_im]
           ring_nf
           done)
    rw [hre2]
    try simp only [← hw]
    ring
  have hexp : Tendsto (fun n : ℕ =>
      Real.exp (((1/2:ℝ) - w.re) * admR n)) atTop (𝓝 0) := by
    have hc' : (0:ℝ) < w.re - 1/2 := by linarith
    have hR : Tendsto (fun n : ℕ => admR n) atTop atTop := tendsto_admR_atTop
    have h1 : Tendsto (fun n : ℕ => (w.re - 1/2) * admR n) atTop atTop := by
      first
        | exact Tendsto.const_mul_atTop hc' hR
        | exact hR.const_mul_atTop hc'
        | exact Filter.Tendsto.const_mul_atTop hc' hR
    have h2 : Tendsto (fun n : ℕ => -((w.re - 1/2) * admR n)) atTop atBot := by
      first
        | exact tendsto_neg_atTop_atBot.comp h1
        | exact Filter.tendsto_neg_atTop_atBot.comp h1
        | exact h1.neg_atBot
    apply Real.tendsto_exp_atBot.comp
    exact h2.congr (fun n => by ring)
  have hlim := hexp.const_mul (‖(1:ℂ) / ((2:ℂ)*w)‖ / ‖(1/2:ℂ) - w‖)
  rw [mul_zero] at hlim
  exact Tendsto.congr (fun n => (hnorm n).symm) hlim

#print axioms compensatorM
#print axioms zero_not_mem_Omega
#print axioms sqrt_ne_half
#print axioms sqrt_ne_zero'
#print axioms compensatorM_overlap0

end

end RHFormalization
