import RHFormalization.CanonicalPrimePowerHeatKernelPrimePowerSupport

/-!
# RHFormalization.CanonicalPrimePowerHeatKernelLogGaussianTail

Log-Gaussian tail estimate for the heat-kernel prime-power summability theorem.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Eventually, the log-Gaussian tail beats `n^(-3)`.

This is the analytic estimate needed to dominate the heat-kernel
prime-power summand by a summable p-series-type majorant.
-/
theorem eventually_exp_neg_log_sq_le_inv_cube
    (t : ℝ)
    (ht : 0 < t) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-(Real.log (n : ℝ)) ^ 2 / (4 * t)) ≤
        ((n : ℝ) ^ 3)⁻¹ := by
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop := by
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

  have h_event_log :
      ∀ᶠ n : ℕ in Filter.atTop,
        12 * t ≤ Real.log (n : ℝ) :=
    (tendsto_atTop.1 hlog_atTop) (12 * t)

  have h_event_pos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < (n : ℝ) := by
    exact eventually_atTop.2 ⟨1, by
      intro n hn
      exact_mod_cast Nat.succ_le_iff.mp hn⟩

  filter_upwards [h_event_log, h_event_pos] with n hlog hnpos

  set u : ℝ := Real.log (n : ℝ)

  have ht4 : 0 < 4 * t := by
    nlinarith

  have hu_ge : 12 * t ≤ u := by
    simpa [u] using hlog

  have hu_nonneg : 0 ≤ u := by
    nlinarith

  have hquad : 3 * u ≤ u ^ 2 / (4 * t) := by
    have hmul : (3 * u) * (4 * t) ≤ u ^ 2 := by
      nlinarith
    exact (le_div_iff₀ ht4).2 hmul

  have hneg : -u ^ 2 / (4 * t) ≤ -(3 * u) := by
    have hneg_core : -(u ^ 2 / (4 * t)) ≤ -(3 * u) := by
      exact neg_le_neg hquad
    simpa [neg_div] using hneg_core

  have hexp_le :
      Real.exp (-u ^ 2 / (4 * t)) ≤ Real.exp (-(3 * u)) :=
    Real.exp_le_exp.mpr hneg

  have h_exp_rhs :
      Real.exp (-(3 * u)) = ((n : ℝ) ^ 3)⁻¹ := by
    have h3 :
        Real.exp (3 * Real.log (n : ℝ)) = (n : ℝ) ^ 3 := by
      calc
        Real.exp (3 * Real.log (n : ℝ))
            = Real.exp (Real.log (n : ℝ)) ^ 3 := by
                simpa [mul_comm] using
                  (Real.exp_nat_mul (Real.log (n : ℝ)) 3)
        _ = (n : ℝ) ^ 3 := by
                rw [Real.exp_log hnpos]
    rw [Real.exp_neg]
    simpa [u, h3]

  simpa [u, h_exp_rhs] using hexp_le

end

end RHFormalization
