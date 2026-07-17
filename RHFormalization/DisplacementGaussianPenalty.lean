import Mathlib

/-!
# Displacement Gaussian penalty: `exp(-δ²/(cτ)) ≤ C·τ^N`

Linchpin of Appendix-D super-smoothing (Lemma B.MIX / D.DISP-BOUND): the off-diagonal
Gaussian penalty `exp(-δ²/(cτ))` from cluster separation `δ > 0` decays faster than
every power `τ^N` as `τ → 0⁺`. The per-word time-decay that, summed over the simplex,
yields the mixed-word remainder's `SuperPolynomialDecay`.

Proof: single-term lower bound `exp x ≥ x^N/N!` (`Real.pow_div_factorial_le_exp`) at
`x = δ²/(cτ)`, inverted via `inv_anti₀`. Explicit `C = N!·c^N/δ^{2N}`; holds for ALL `τ > 0`.
-/

namespace RHFormalization
open Real
noncomputable section

/-- **Displacement Gaussian penalty (B.MIX linchpin).**
`exp(-δ²/(cτ)) ≤ (N!·c^N/δ^{2N})·τ^N` for all `τ > 0`, given `δ,c > 0`. -/
theorem gaussian_penalty_le_pow
    (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) (N : ℕ) :
    ∀ τ : ℝ, 0 < τ →
      Real.exp (-(δ ^ 2 / (c * τ)))
        ≤ ((Nat.factorial N : ℝ) * c ^ N / δ ^ (2 * N)) * τ ^ N := by
  intro τ hτ
  have hfact_pos : 0 < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  set x : ℝ := δ ^ 2 / (c * τ) with hxdef
  have hx_pos : 0 < x := by rw [hxdef]; positivity
  have hxN_pos : 0 < x ^ N := pow_pos hx_pos N
  have hlow : x ^ N / (Nat.factorial N : ℝ) ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp x hx_pos.le N
  have hquot_pos : 0 < x ^ N / (Nat.factorial N : ℝ) := div_pos hxN_pos hfact_pos
  have hbound : Real.exp (-x) ≤ (Nat.factorial N : ℝ) / x ^ N := by
    have hone : 1 / Real.exp x ≤ 1 / (x ^ N / (Nat.factorial N : ℝ)) :=
      one_div_le_one_div_of_le hquot_pos hlow
    rw [Real.exp_neg, ← one_div]
    rw [one_div_div] at hone
    exact hone
  have heq : (Nat.factorial N : ℝ) / x ^ N
      = ((Nat.factorial N : ℝ) * c ^ N / δ ^ (2 * N)) * τ ^ N := by
    rw [hxdef, div_pow]
    rw [show (δ ^ 2) ^ N = δ ^ (2 * N) by rw [← pow_mul]]
    rw [mul_pow]
    field_simp
  rw [show Real.exp (-(δ ^ 2 / (c * τ))) = Real.exp (-x) by rw [hxdef]]
  rw [← heq]
  exact hbound

#print axioms gaussian_penalty_le_pow
end
end RHFormalization
