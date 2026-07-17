import RHFormalization.ShiftedLaplaceRepRestAtWitness
import RHFormalization.EnvelopeFromZeroDensity
import RHFormalization.PairPoleIsolation

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

theorem polePoint_eq_iff (a b : ℂ) :
    polePoint a = polePoint b ↔ a = b ∨ a = 1 - b := by
  unfold polePoint
  constructor
  · intro h
    have h2 : a * (1 - a) = b * (1 - b) := neg_injective h
    have hfac : (a - b) * (a + b - 1) = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp hfac with h3 | h3
    · left; exact sub_eq_zero.mp h3
    · right; linear_combination h3
  · rintro (h | h) <;> rw [h] <;> ring

theorem denom_lower_bound_witness_ball
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re < 1/2 → ρ ≠ ρrep →
        ∀ s ∈ Metric.closedBall W.s0 R, c * (1 + ρ.im ^ 2) ≤ ‖zeroPoleDenom ρ s‖ := by
  set C : ℝ := ‖W.s0‖ + R with hCdef
  have hCnn : (0:ℝ) ≤ C := by
    have : (0:ℝ) ≤ ‖W.s0‖ := norm_nonneg _
    rw [hCdef]; linarith
  have hbnd : ∀ s ∈ Metric.closedBall W.s0 R, ‖s‖ ≤ C := by
    intro s hs
    rw [Metric.mem_closedBall] at hs
    have hsr : ‖s - W.s0‖ ≤ R := by rw [← dist_eq_norm]; exact hs
    calc ‖s‖ = ‖W.s0 + (s - W.s0)‖ := by ring_nf
      _ ≤ ‖W.s0‖ + ‖s - W.s0‖ := norm_add_le _ _
      _ ≤ ‖W.s0‖ + R := by linarith
      _ = C := by rw [hCdef]
  have h2C3 : (0:ℝ) < 2 * C + 3 := by linarith
  refine ⟨min (1/2) (R / (2*C + 3)),
    lt_min (by norm_num) (div_pos hR h2C3), ?_⟩
  intro ρ hρ hρre hne s hs
  rw [norm_zeroPoleDenom_eq_dist]
  rcases le_total (2*C + 2) (ρ.im ^ 2) with hbig | hsmall
  · have h1 : ρ.im ^ 2 ≤ ‖polePoint ρ‖ :=
      im_sq_le_norm_polePoint ρ (le_of_lt hρ.2.1) (le_of_lt hρ.2.2)
    have h2 : ‖polePoint ρ‖ - ‖s‖ ≤ dist s (polePoint ρ) := by
      rw [dist_eq_norm, ← norm_sub_rev]; exact norm_sub_norm_le _ _
    have h3 : ‖s‖ ≤ C := hbnd s hs
    have h5 : (1 + ρ.im ^ 2) / 2 ≤ dist s (polePoint ρ) := by linarith
    have hnn : (0:ℝ) ≤ 1 + ρ.im ^ 2 := by positivity
    calc min (1/2) (R/(2*C+3)) * (1 + ρ.im ^ 2)
        ≤ (1/2) * (1 + ρ.im ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hnn
      _ = (1 + ρ.im ^ 2) / 2 := by ring
      _ ≤ dist s (polePoint ρ) := h5
  · have hne1 : ρ ≠ W.ρ := by
      intro hc
      apply hne
      have hpp : polePoint ρ = polePoint ρrep := by
        rw [hc, ← W.hs0_def]; exact hρrep_pole.symm
      rcases (polePoint_eq_iff ρ ρrep).mp hpp with he | he
      · exact he
      · exfalso
        have hre' : ρ.re = 1 - ρrep.re := by rw [he]; simp [Complex.sub_re, Complex.one_re]
        linarith
    have hne2 : ρ ≠ 1 - W.ρ := by
      intro hc
      apply hne
      have hpp : polePoint ρ = polePoint ρrep := by
        have hpe : polePoint (1 - W.ρ) = polePoint W.ρ := by unfold polePoint; ring
        rw [hc, hpe, ← W.hs0_def]; exact hρrep_pole.symm
      rcases (polePoint_eq_iff ρ ρrep).mp hpp with he | he
      · exact he
      · exfalso
        have hre' : ρ.re = 1 - ρrep.re := by rw [he]; simp [Complex.sub_re, Complex.one_re]
        linarith
    have hdist : 2 * R ≤ dist (polePoint ρ) W.s0 := hRiso ρ hρ hne1 hne2
    have hs' : dist s W.s0 ≤ R := by rw [Metric.mem_closedBall] at hs; exact hs
    have htri : R ≤ dist s (polePoint ρ) := by
      have htri0 : dist (polePoint ρ) W.s0 ≤ dist (polePoint ρ) s + dist s W.s0 :=
        dist_triangle _ _ _
      rw [dist_comm (polePoint ρ) s] at htri0
      linarith
    have h2 : 1 + ρ.im ^ 2 ≤ 2*C + 3 := by nlinarith
    have hnn : (0:ℝ) ≤ 1 + ρ.im ^ 2 := by positivity
    have hq : (0:ℝ) ≤ R / (2*C+3) := le_of_lt (div_pos hR h2C3)
    calc min (1/2) (R/(2*C+3)) * (1 + ρ.im ^ 2)
        ≤ (R/(2*C+3)) * (1 + ρ.im ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hnn
      _ ≤ (R/(2*C+3)) * (2*C+3) := mul_le_mul_of_nonneg_left h2 hq
      _ = R := by field_simp
      _ ≤ dist s (polePoint ρ) := htri

#print axioms polePoint_eq_iff
#print axioms denom_lower_bound_witness_ball

noncomputable def witnessDenomConst
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0) : ℝ :=
  (denom_lower_bound_witness_ball W ρrep hρrep_re hρrep_pole R hR hRiso).choose

theorem witnessDenomConst_pos
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0) :
    0 < witnessDenomConst W ρrep hρrep_re hρrep_pole R hR hRiso :=
  (denom_lower_bound_witness_ball W ρrep hρrep_re hρrep_pole R hR hRiso).choose_spec.1

theorem witnessDenomConst_le
    (W : ZeroWitness) (ρrep : ℂ)
    (hρrep_re : ρrep.re < 1/2)
    (hρrep_pole : polePoint ρrep = W.s0)
    (R : ℝ) (hR : 0 < R)
    (hRiso : ∀ ρ' : ℂ, IsNontrivialZetaZero ρ' → ρ' ≠ W.ρ → ρ' ≠ 1 - W.ρ →
      2 * R ≤ dist (polePoint ρ') W.s0) :
    ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re < 1/2 → ρ ≠ ρrep →
      ∀ s ∈ Metric.closedBall W.s0 R,
        witnessDenomConst W ρrep hρrep_re hρrep_pole R hR hRiso * (1 + ρ.im ^ 2)
          ≤ ‖zeroPoleDenom ρ s‖ :=
  (denom_lower_bound_witness_ball W ρrep hρrep_re hρrep_pole R hR hRiso).choose_spec.2

#print axioms witnessDenomConst
#print axioms witnessDenomConst_le

end
end RHFormalization
