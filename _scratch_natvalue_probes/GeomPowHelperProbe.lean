import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

lemma two_pow_le_prime_pow_three_mul_probe
    {p k : ℕ} (hp : 2 ≤ p) :
    (2 : ℝ) ^ k ≤ (p : ℝ) ^ (3 * k) := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hp3 : (2 : ℝ) ≤ (p : ℝ) ^ 3 := by
        nlinarith [sq_nonneg (p : ℝ), hpR]
      calc
        (2 : ℝ) ^ (k + 1)
            = (2 : ℝ) ^ k * 2 := by
              rw [pow_succ]
        _ ≤ (p : ℝ) ^ (3 * k) * (p : ℝ) ^ 3 := by
              exact mul_le_mul ih hp3 (by norm_num) (by positivity)
        _ = (p : ℝ) ^ (3 * (k + 1)) := by
              rw [← pow_add]
              congr 1

end RHFormalization
