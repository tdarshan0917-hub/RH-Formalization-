import Mathlib
set_option autoImplicit false
open Real Filter

namespace RHFormalization

/-- Geometric summability of `∑ e^{-k}` (ratio `e^{-1} < 1`). -/
theorem summable_exp_neg_nat :
    Summable (fun k : ℕ => Real.exp (-(k : ℝ))) := by
  have heq : (fun k : ℕ => Real.exp (-(k : ℝ)))
      = (fun k : ℕ => (Real.exp (-1)) ^ k) := by
    funext k; rw [← Real.exp_nat_mul]; ring_nf
  rw [heq]
  apply summable_geometric_of_lt_one (by positivity)
  rw [Real.exp_lt_one_iff]; norm_num

/-- **A.ENV-DOM, shell summability.** `(k+1)·e^{k/2}·e^{-c·k²}` is summable over
`k` for any `c > 0`: Gaussian decay dominates sub-exponential growth. Bounded
pointwise by `C·e^{-k}` with `C = e^{25/(16c)}` (manuscript p.55). -/
theorem summable_shell_coeff (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℕ =>
      ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-c * (k : ℝ) ^ 2)) := by
  have hnn : ∀ k : ℕ,
      0 ≤ ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-c * (k : ℝ) ^ 2) := by
    intro k; positivity
  set C : ℝ := Real.exp (25 / (16 * c)) with hC_def
  -- dominating summable function: C · e^{-k}
  have hdom : Summable (fun k : ℕ => C * Real.exp (-(k : ℝ))) :=
    summable_exp_neg_nat.mul_left C
  apply Summable.of_nonneg_of_le hnn ?_ hdom
  intro k
  -- (k+1)·e^{k/2}·e^{-ck²} ≤ C·e^{-k}
  -- Step A: (k+1) ≤ e^k
  have hk1 : ((k : ℝ) + 1) ≤ Real.exp (k : ℝ) := by
    have := Real.add_one_le_exp (k : ℝ); linarith
  have hexpk_pos : 0 < Real.exp ((k : ℝ) / 2) := Real.exp_pos _
  have hexpck_pos : 0 < Real.exp (-c * (k : ℝ) ^ 2) := Real.exp_pos _
  -- LHS ≤ e^k · e^{k/2} · e^{-ck²}
  have hstepA : ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-c * (k : ℝ) ^ 2)
      ≤ Real.exp (k : ℝ) * Real.exp ((k : ℝ) / 2) * Real.exp (-c * (k : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hexpck_pos)
    apply mul_le_mul_of_nonneg_right hk1 (le_of_lt hexpk_pos)
  -- merge exponents: e^k·e^{k/2}·e^{-ck²} = e^{3k/2 - ck²}
  have hmerge : Real.exp (k : ℝ) * Real.exp ((k : ℝ) / 2) * Real.exp (-c * (k : ℝ) ^ 2)
      = Real.exp (3 * (k : ℝ) / 2 - c * (k : ℝ) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  -- RHS = C·e^{-k} = e^{25/(16c)}·e^{-k} = e^{25/(16c) - k}
  have hRHS : C * Real.exp (-(k : ℝ)) = Real.exp (25 / (16 * c) - (k : ℝ)) := by
    rw [hC_def, ← Real.exp_add]; ring_nf
  rw [hRHS]
  refine le_trans hstepA (le_of_eq_of_le hmerge ?_)
  apply Real.exp_le_exp.mpr
  -- 3k/2 - ck² ≤ 25/(16c) - k  ⟺  5k/2 - ck² ≤ 25/(16c)  ⟺  0 ≤ c(k - 5/(4c))²
  have hsq : 0 ≤ c * ((k : ℝ) - 5 / (4 * c)) ^ 2 :=
    mul_nonneg (le_of_lt hc) (sq_nonneg _)
  have hexpand : c * ((k : ℝ) - 5 / (4 * c)) ^ 2
      = c * (k : ℝ) ^ 2 - 5 * (k : ℝ) / 2 + 25 / (16 * c) := by
    field_simp; ring
  nlinarith [hsq, hexpand]

#print axioms summable_exp_neg_nat
#print axioms summable_shell_coeff

end RHFormalization
