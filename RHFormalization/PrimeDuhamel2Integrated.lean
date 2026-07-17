import RHFormalization.PrimeDuhamel2IntegrandSqrt
import RHFormalization.Duhamel2IntegratedBound
import RHFormalization.BetaConvBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- `primeDuhamel2Integrand μ V t ·` is continuous in `u`. -/
theorem primeDuhamel2Integrand_continuous
    (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    Continuous (fun u : ℝ => primeDuhamel2Integrand μ V t u) := by
  simp only [primeDuhamel2Integrand_eq_sum]
  apply continuous_finset_sum; intro m _
  apply continuous_finset_sum; intro n _
  apply Continuous.mul
  apply Continuous.mul
  apply Continuous.mul
  · exact continuous_const
  · apply Complex.continuous_exp.comp
    apply Continuous.mul
    · apply Continuous.neg
      apply Continuous.comp Complex.continuous_ofReal
      apply Continuous.sub continuous_const continuous_id
    · exact continuous_const
  · exact continuous_const
  · apply Complex.continuous_exp.comp
    apply Continuous.mul
    · apply Continuous.neg
      apply Continuous.comp Complex.continuous_ofReal continuous_id
    · exact continuous_const

/-- **Brick 3c (integrated bound).** The time integral of the prime order-2 Duhamel
integrand is bounded by a `t`-independent-shaped constant (the `O(t^{1/2})` super-smoothing):
`∫₀ᵗ ‖·‖ du ≤ B²·e^{tM}·(L/(2√π))²·4`. -/
theorem integral_norm_primeDuhamel2Integrand_le
    (L : ℝ) (hL : 0 < L) (M : ℝ) (B : ℝ) (hB : 0 ≤ B)
    (t : ℝ) (ht : 0 < t)
    (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ)
    (hVB : ∀ i j, ‖V i j‖ ≤ B)
    (hμ : ∀ n : Fin N, ((((n : ℝ) + 1) * Real.pi / L) ^ 2) - M ≤ μ n) :
    ∫ u in (0:ℝ)..t, ‖primeDuhamel2Integrand μ V t u‖
      ≤ B ^ 2 * Real.exp (t * M) * ((L / (2 * Real.sqrt Real.pi)) ^ 2) * 4 := by
  set K := B ^ 2 * Real.exp (t * M) * ((L / (2 * Real.sqrt Real.pi)) ^ 2) with hK
  -- pointwise: ‖·‖ ≤ K·((t-u)^{-1/2} u^{-1/2})
  have hpt : ∀ u ∈ Set.Ioo (0:ℝ) t,
      ‖primeDuhamel2Integrand μ V t u‖
        ≤ K * ((t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) := by
    intro u hu
    obtain ⟨hu0, hut⟩ := hu
    have htu : 0 < t - u := by linarith
    refine le_trans (norm_primeDuhamel2Integrand_le_sqrt L hL M B hB t u hu0 htu μ V hVB hμ) ?_
    rw [sqrt_heat_factor L (t - u) hL htu, sqrt_heat_factor L u hL hu0]
    apply le_of_eq
    have hexp : Real.exp ((t - u) * M) * Real.exp (u * M) = Real.exp (t * M) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hK]
    -- both sides are products; substitute the exp-merge then ring
    rw [← hexp]
    ring
  have hint_lhs : IntervalIntegrable
      (fun u : ℝ => ‖primeDuhamel2Integrand μ V t u‖) volume 0 t :=
    (primeDuhamel2Integrand_continuous μ V t).norm.intervalIntegrable 0 t
  have hint_rhs : IntervalIntegrable
      (fun u : ℝ => K * ((t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2))) volume 0 t :=
    (intervalIntegrable_beta_integrand t ht).const_mul K
  calc ∫ u in (0:ℝ)..t, ‖primeDuhamel2Integrand μ V t u‖
      ≤ ∫ u in (0:ℝ)..t, K * ((t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) :=
        intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint_lhs hint_rhs hpt
    _ = K * ∫ u in (0:ℝ)..t, (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ K * 4 := by
        apply mul_le_mul_of_nonneg_left (beta_conv_bound t ht)
        rw [hK]; positivity
    _ = B ^ 2 * Real.exp (t * M) * ((L / (2 * Real.sqrt Real.pi)) ^ 2) * 4 := by rw [hK]

#print axioms integral_norm_primeDuhamel2Integrand_le

end
end RHFormalization
