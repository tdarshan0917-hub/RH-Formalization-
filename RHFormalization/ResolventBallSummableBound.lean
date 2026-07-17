import RHFormalization.BallCutDistance
import RHFormalization.ResolventLocalBound
import RHFormalization.EigenvalueGrowthSummable
import RHFormalization.ResolventTraceHolo

/-!
# RHFormalization.ResolventBallSummableBound
Multiplicative lower bound `‖s+λ‖ ≥ c'·(1+λ)` on a ball ⊆ Ω, combining the
cut-distance bound (small λ) and the real-part bound (large λ).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric

theorem re_add_le_norm_add (s : ℂ) (lam : ℝ) :
    s.re + lam ≤ ‖s + (lam : ℂ)‖ := by
  have h := re_le_norm (s + (lam : ℂ))
  simpa [Complex.add_re, Complex.ofReal_re] using h

theorem exists_mul_lower_bound_on_ball
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall c r ⊆ Ω) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ s ∈ Metric.closedBall c r, ∀ lam : ℝ, 0 ≤ lam →
      c' * (1 + lam) ≤ ‖s + (lam : ℂ)‖ := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_lower_bound_on_ball c r hr hball
  set R0 : ℝ := ‖c‖ + r with hR0def
  have hR0nonneg : 0 ≤ R0 := by positivity
  have hsbound : ∀ s ∈ Metric.closedBall c r, ‖s‖ ≤ R0 := by
    intro s hs
    have hd : dist s c ≤ r := by rwa [Metric.mem_closedBall] at hs
    calc ‖s‖ = ‖c + (s - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖s - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + r := by rw [← dist_eq_norm] at *; linarith [hd]
  refine ⟨min δ 1 / (2 + 2 * R0), by positivity, ?_⟩
  intro s hsmem lam hlam
  have hsnorm : ‖s‖ ≤ R0 := hsbound s hsmem
  have hδs : δ ≤ ‖s + (lam : ℂ)‖ := hδ s hsmem lam hlam
  have hre : s.re + lam ≤ ‖s + (lam : ℂ)‖ := re_add_le_norm_add s lam
  have hres : -R0 ≤ s.re := by
    have := abs_re_le_norm s; rw [abs_le] at this; linarith [this.1, hsnorm]
  have hmin_le : min δ 1 ≤ δ := min_le_left _ _
  have hmin_pos : 0 < min δ 1 := lt_min hδpos one_pos
  have hle1 : min δ 1 ≤ 1 := min_le_right _ _
  have hdenpos : (0:ℝ) < 2 + 2 * R0 := by positivity
  rcases le_or_gt lam (1 + 2 * R0) with hsmall | hbig
  · -- small λ : c'(1+λ) ≤ min δ 1 ≤ δ ≤ ‖s+λ‖
    have h1 : (1 + lam) ≤ 2 + 2 * R0 := by linarith
    have hstep : min δ 1 / (2 + 2 * R0) * (1 + lam) ≤ min δ 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hdenpos]
      nlinarith [hmin_pos, h1, hmin_le, hR0nonneg]
    linarith [hstep, hmin_le, hδs]
  · -- large λ : c'(1+λ) ≤ (1+λ)/2 ≤ λ-R0 ≤ s.re+λ ≤ ‖s+λ‖
    have h1lam_pos : 0 ≤ 1 + lam := by linarith
    have hc'le : min δ 1 / (2 + 2 * R0) ≤ 1 / 2 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [hle1, hR0nonneg]
    have hstep : min δ 1 / (2 + 2 * R0) * (1 + lam) ≤ (1 + lam) / 2 := by
      have := mul_le_mul_of_nonneg_right hc'le h1lam_pos
      calc min δ 1 / (2 + 2 * R0) * (1 + lam)
          ≤ (1 / 2) * (1 + lam) := this
        _ = (1 + lam) / 2 := by ring
    have hhalf : (1 + lam) / 2 ≤ lam - R0 := by linarith
    calc min δ 1 / (2 + 2 * R0) * (1 + lam)
        ≤ (1 + lam) / 2 := hstep
      _ ≤ lam - R0 := hhalf
      _ ≤ s.re + lam := by linarith [hres]
      _ ≤ ‖s + (lam : ℂ)‖ := hre

#print axioms re_add_le_norm_add
#print axioms exists_mul_lower_bound_on_ball
