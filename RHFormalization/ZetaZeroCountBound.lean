import Mathlib.Analysis.Complex.JensenFormula
import RHFormalization.CompletedZetaGrowth
import RHFormalization.CompletedZetaMeromorphic

/-!
# Jensen disk-count bound for `Λ₀`

Applies Mathlib's `AnalyticOnNhd.sum_divisor_le` (Jensen's counting formula) to the completed
Riemann zeta `Λ₀`, using the finite-order envelope `completedZeta0_order_bound` and the concrete
nonzero point `completedZeta0_ne_zero_at_two`. The center is `c = 2` (where `Λ₀ 2 = (π-3)/6 ≠ 0`),
and the result bounds the total zero multiplicity of `Λ₀` in `closedBall 2 R` by `O(R²)`.
-/

namespace RHFormalization
open Complex Real MeasureTheory Set MeromorphicOn Metric

/-- **Jensen disk-count bound.** The total zero multiplicity of `Λ₀` in `closedBall 2 R`
is `≤ C·(3 + 2R)² + D` for constants `C ≥ 0`, `D`. (Crude `O(R²)` rate.) -/
theorem completedZeta0_disk_count_le :
    ∃ (C D : ℝ), 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ᶠ u, divisor completedRiemannZeta₀ (closedBall (2:ℂ) |R|) u
        ≤ C * (3 + 2 * R) ^ 2 + D := by
  obtain ⟨K0, hK00, hbound⟩ := completedZeta0_order_bound
  -- constants for the final affine bound
  refine ⟨K0 / Real.log 2, (- Real.log ‖completedRiemannZeta₀ 2‖) / Real.log 2, ?_, ?_⟩
  · positivity
  intro R hR
  have hRpos : 0 < R := by linarith
  have hr_pos : 0 < |R| := by rw [abs_of_pos hRpos]; exact hRpos
  have hr_lt_R : |R| < |2 * R| := by
    rw [abs_of_pos hRpos, abs_of_pos (by linarith : (0:ℝ) < 2 * R)]; linarith
  -- The sphere bound M = exp(K0 (3+2R)^2)
  set M : ℝ := Real.exp (K0 * (3 + 2 * R) ^ 2) with hM
  have hM1 : 1 ≤ M := by rw [hM, Real.one_le_exp_iff]; positivity
  -- analytic on the ball
  have h₁f : AnalyticOnNhd ℂ completedRiemannZeta₀ (closedBall (2:ℂ) |2 * R|) :=
    completedZeta₀_analyticOnNhd.mono (Set.subset_univ _)
  -- nonzero at center
  have h₂f : completedRiemannZeta₀ 2 ≠ 0 := completedZeta0_ne_zero_at_two
  -- bound on the sphere of radius |2R| around 2
  have f_bound : ∀ z ∈ sphere (2:ℂ) |2 * R|, ‖completedRiemannZeta₀ z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    -- ‖z‖ ≤ ‖2‖ + ‖z - 2‖ = 2 + |2R| = 2 + 2R
    have hznorm : ‖z‖ ≤ 2 + 2 * R := by
      have h1 : ‖z‖ ≤ ‖(2:ℂ)‖ + ‖z - 2‖ := by
        calc ‖z‖ = ‖(2:ℂ) + (z - 2)‖ := by ring_nf
          _ ≤ ‖(2:ℂ)‖ + ‖z - 2‖ := norm_add_le _ _
      rw [hz, abs_of_pos (by linarith : (0:ℝ) < 2 * R)] at h1
      have h2 : ‖(2:ℂ)‖ = 2 := by simp
      rw [h2] at h1; linarith
    refine le_trans (hbound z) ?_
    rw [hM]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hK00
    have : (1 + ‖z‖) ≤ (3 + 2 * R) := by linarith
    nlinarith [norm_nonneg z, this, hR]
  -- apply Jensen
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := 2) (r := R) (R := 2 * R) (M := M)
    hr_pos hr_lt_R hM1 h₁f h₂f f_bound
  -- RHS = log(M/‖Λ₀ 2‖)/log(2R/R) = log(M/‖Λ₀ 2‖)/log 2
  refine le_trans hjensen ?_
  -- simplify log(2R/R) = log 2
  have hlog2R : Real.log (2 * R / R) = Real.log 2 := by
    rw [mul_div_assoc, div_self (ne_of_gt hRpos), mul_one]
  rw [hlog2R]
  -- log(M/‖Λ₀ 2‖) = log M - log‖Λ₀ 2‖ = K0(3+2R)^2 - log‖Λ₀ 2‖
  have hnorm_pos : 0 < ‖completedRiemannZeta₀ 2‖ := by
    rw [norm_pos_iff]; exact h₂f
  have hMpos : 0 < M := Real.exp_pos _
  have hlogM : Real.log (M / ‖completedRiemannZeta₀ 2‖)
      = K0 * (3 + 2 * R) ^ 2 - Real.log ‖completedRiemannZeta₀ 2‖ := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hnorm_pos), hM, Real.log_exp]
  rw [hlogM]
  -- RHS goal: LHS = RHS (just distributing /log2), so close by le_of_eq
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  apply le_of_eq
  field_simp
  ring

#print axioms completedZeta0_disk_count_le
