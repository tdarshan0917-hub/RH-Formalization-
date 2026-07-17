import Mathlib
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **A.ENV-DOM, u≤0 positional inequality.** For `u ≤ 0` and `k ≥ 0`, the
displacement satisfies `(u−k)² ≥ u² + k²`. Since `u ≤ 0 ≤ k`, the cross term
`−2uk ≥ 0`. This is the `u≤0` branch of the shell-sum estimate (manuscript p.55,
where it appears as `(u−k)² ≥ c(u²+k²)` with `c=1` here). -/
theorem shell_neg_position (u : ℝ) (hu : u ≤ 0) (k : ℕ) :
    (u - (k : ℝ)) ^ 2 ≥ u ^ 2 + (k : ℝ) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [mul_nonneg (neg_nonneg.mpr hu) hk]

/-- **A.ENV-DOM, u≤0 Gaussian bound.** For `u ≤ 0`, `k ≥ 0`, `0 < κ'`, the
localized Gaussian at shell `k` is bounded by a product that factors the
`u`-dependence: `e^{-κ'(u−k)²} ≤ e^{-κ'u²}·e^{-κ'k²}`. Direct consequence of
`(u−k)² ≥ u² + k²` and exponential monotonicity. -/
theorem shell_neg_gaussian_factor
    (u : ℝ) (hu : u ≤ 0) (k : ℕ) (κ' : ℝ) (hκ' : 0 < κ') :
    Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ Real.exp (-κ' * u ^ 2) * Real.exp (-κ' * (k : ℝ) ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hpos := shell_neg_position u hu k
  nlinarith [hpos, hκ']

#print axioms shell_neg_position
#print axioms shell_neg_gaussian_factor

end RHFormalization
