import RHFormalization.PrimeWellEnvelopeLemmaB

/-!
# Prime-well envelope (DQ1), Lemma C: weighted shell bound

On a dyadic shell `n ∈ (2^k, 2^(k+1)]`, the weight `1/√n ≤ 2^(-k/2)`, so the
weighted von Mangoldt mass is `≤ 2(log4+4)·2^(k/2)` via Lemma B.
-/

namespace RHFormalization

open Chebyshev ArithmeticFunction Finset Real

/-- The Chebyshev shell-mass bound specialised to dyadic naturals. -/
theorem vonMangoldt_dyadic_mass_le (k : ℕ) :
    ∑ n ∈ Finset.Ioc (2^k) (2^(k+1)), vonMangoldt n
      ≤ (Real.log 4 + 4) * (2^(k+1) : ℝ) := by
  have hb := vonMangoldt_shell_mass_le ((2:ℝ)^k) ((2:ℝ)^(k+1))
    (by positivity) (by positivity)
    (by apply pow_le_pow_right₀ (by norm_num); omega)
  have hfk : ⌊((2:ℝ)^k)⌋₊ = 2^k := by
    rw [show ((2:ℝ)^k) = ((2^k : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hfk1 : ⌊((2:ℝ)^(k+1))⌋₊ = 2^(k+1) := by
    rw [show ((2:ℝ)^(k+1)) = ((2^(k+1) : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rwa [hfk, hfk1] at hb

/-- **Lemma C (weighted shell bound).** -/
theorem weighted_shell_bound (k : ℕ) :
    ∑ n ∈ Finset.Ioc (2^k) (2^(k+1)), vonMangoldt n / Real.sqrt n
      ≤ 2 * (Real.log 4 + 4) * Real.sqrt (2^k) := by
  have hsqrt_pos : 0 < Real.sqrt ((2:ℝ)^k) := Real.sqrt_pos.mpr (by positivity)
  have hterm : ∀ n ∈ Finset.Ioc (2^k) (2^(k+1)),
      vonMangoldt n / Real.sqrt n ≤ vonMangoldt n / Real.sqrt (2^k) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn_ge : (2:ℝ)^k ≤ (n:ℝ) := by exact_mod_cast le_of_lt hn.1
    exact div_le_div_of_nonneg_left vonMangoldt_nonneg hsqrt_pos (Real.sqrt_le_sqrt hn_ge)
  have hsq : Real.sqrt ((2:ℝ)^k) * Real.sqrt ((2:ℝ)^k) = (2:ℝ)^k := by
    rw [← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
  -- the key algebraic identity: 2^(k+1)/√(2^k) = 2·√(2^k)
  have hdiv : ((2:ℝ)^(k+1)) / Real.sqrt (2^k) = 2 * Real.sqrt (2^k) := by
    rw [div_eq_iff (ne_of_gt hsqrt_pos), pow_succ]
    nlinarith [hsq]
  calc ∑ n ∈ Finset.Ioc (2^k) (2^(k+1)), vonMangoldt n / Real.sqrt n
      ≤ ∑ n ∈ Finset.Ioc (2^k) (2^(k+1)), vonMangoldt n / Real.sqrt (2^k) :=
        Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.Ioc (2^k) (2^(k+1)), vonMangoldt n) / Real.sqrt (2^k) :=
        (Finset.sum_div _ _ _).symm
    _ ≤ ((Real.log 4 + 4) * (2^(k+1) : ℝ)) / Real.sqrt (2^k) :=
        div_le_div_of_nonneg_right (vonMangoldt_dyadic_mass_le k) hsqrt_pos.le
    _ = (Real.log 4 + 4) * (((2:ℝ)^(k+1)) / Real.sqrt (2^k)) := by ring
    _ = (Real.log 4 + 4) * (2 * Real.sqrt (2^k)) := by rw [hdiv]
    _ = 2 * (Real.log 4 + 4) * Real.sqrt (2^k) := by ring

#print axioms vonMangoldt_dyadic_mass_le
#print axioms weighted_shell_bound

end RHFormalization
