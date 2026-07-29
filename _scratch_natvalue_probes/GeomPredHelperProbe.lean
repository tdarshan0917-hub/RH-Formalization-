import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

lemma two_pow_le_two_prime_pow_three_pred_probe
    {p m : ℕ} (hp : 2 ≤ p) (hm : 0 < m) :
    (2 : ℝ) ^ m ≤ 2 * (p : ℝ) ^ (3 * (m - 1)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨k, rfl⟩
  simp [Nat.succ_eq_add_one]
  calc
    (2 : ℝ) ^ (k + 1)
        = (2 : ℝ) ^ k * 2 := by
          rw [pow_succ]
    _ ≤ (p : ℝ) ^ (3 * k) * 2 := by
          exact
            mul_le_mul_of_nonneg_right
              (two_pow_le_prime_pow_three_mul (p := p) (k := k) hp)
              (by norm_num)
    _ = 2 * (p : ℝ) ^ (3 * k) := by
          ring

end RHFormalization
