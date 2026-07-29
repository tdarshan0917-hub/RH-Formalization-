import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

lemma linear_lower_bound_prime_pow_probe
    {p k : ℕ} (hp : 2 ≤ p) :
    (((p : ℝ) + 1) * ((k + 1 : ℕ) : ℝ)) / 2 ≤
      (p : ℝ) ^ (k + 1) := by
  induction k with
  | zero =>
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      norm_num
      linarith
  | succ k ih =>
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hstep :
          (((p : ℝ) + 1) * (((k + 1 : ℕ) : ℝ) + 1)) / 2 ≤
            ((((p : ℝ) + 1) * ((k + 1 : ℕ) : ℝ)) / 2) * (p : ℝ) := by
        nlinarith
      calc
        (((p : ℝ) + 1) * (((k + 1 : ℕ) : ℝ) + 1)) / 2
            ≤ ((((p : ℝ) + 1) * ((k + 1 : ℕ) : ℝ)) / 2) * (p : ℝ) := hstep
        _ ≤ ((p : ℝ) ^ (k + 1)) * (p : ℝ) := by
            exact mul_le_mul_of_nonneg_right ih (by positivity)
        _ = (p : ℝ) ^ ((k + 1) + 1) := by
            rw [pow_succ]

end RHFormalization
