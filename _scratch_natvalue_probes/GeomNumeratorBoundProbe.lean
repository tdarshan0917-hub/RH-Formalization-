import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

lemma geom_numerator_bound_probe
    {p m : ℕ} (hp : 2 ≤ p) (hm : 0 < m) :
    (p : ℝ) * ((p : ℝ) + 1)^2 * (2 : ℝ)^m
      ≤ 8 * (p : ℝ) ^ (3 * m) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity

  have hp1_le_2p : (p : ℝ) + 1 ≤ 2 * (p : ℝ) := by
    nlinarith

  have hp1_sq_le : ((p : ℝ) + 1)^2 ≤ (2 * (p : ℝ))^2 := by
    exact pow_le_pow_left₀ (by positivity) hp1_le_2p 2

  have hfirst :
      (p : ℝ) * ((p : ℝ) + 1)^2 ≤ 4 * (p : ℝ)^3 := by
    have h :=
      mul_le_mul_of_nonneg_left hp1_sq_le hp_nonneg
    nlinarith [h]

  have htwo :
      (2 : ℝ)^m ≤ 2 * (p : ℝ) ^ (3 * (m - 1)) :=
    two_pow_le_two_prime_pow_three_pred (p := p) (m := m) hp hm

  have hprod :
      ((p : ℝ) * ((p : ℝ) + 1)^2) * (2 : ℝ)^m
        ≤ (4 * (p : ℝ)^3) * (2 * (p : ℝ) ^ (3 * (m - 1))) := by
    exact
      mul_le_mul
        hfirst
        htwo
        (by positivity)
        (by positivity)

  have hexp : 3 + 3 * (m - 1) = 3 * m := by
    omega

  calc
    (p : ℝ) * ((p : ℝ) + 1)^2 * (2 : ℝ)^m
        = ((p : ℝ) * ((p : ℝ) + 1)^2) * (2 : ℝ)^m := by
          ring
    _ ≤ (4 * (p : ℝ)^3) * (2 * (p : ℝ) ^ (3 * (m - 1))) := hprod
    _ = 8 * ((p : ℝ)^3 * (p : ℝ) ^ (3 * (m - 1))) := by
          ring
    _ = 8 * (p : ℝ) ^ (3 + 3 * (m - 1)) := by
          rw [← pow_add]
    _ = 8 * (p : ℝ) ^ (3 * m) := by
          rw [hexp]

end RHFormalization
