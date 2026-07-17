import RHFormalization.GalerkinMatrices
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Brick 2, stone 7: uniform-in-N bound on the heat-kernel sum
`∑_{m : Fin N} e^{-t·λ_m} ≤ (1 - e^{-t·c})⁻¹`, uniformly in N, when `λ_m ≥ c·m`,
`c,t > 0`. The heat-decay half of the Duhamel control: composed with stone 6,
gives a cutoff-independent trace bound. Geometric majorization + sum_le_tsum.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real
open scoped BigOperators

variable {N : ℕ}

/-- **Stone 7 (abstract)**: heat-kernel sum bounded by geometric tsum, uniform in N. -/
theorem sum_exp_neg_le_geometric
    (lam : ℕ → ℝ) (c t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (hgrowth : ∀ m : ℕ, c * (m : ℝ) ≤ lam m) :
    ∑ m : Fin N, Real.exp (-(t * lam m)) ≤ (1 - Real.exp (-(t * c)))⁻¹ := by
  set r : ℝ := Real.exp (-(t * c)) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt_one : r < 1 := by
    rw [hr_def, Real.exp_lt_one_iff]
    have : 0 < t * c := mul_pos ht hc
    linarith
  have hterm : ∀ m : ℕ, Real.exp (-(t * lam m)) ≤ r ^ m := by
    intro m
    rw [hr_def, ← Real.exp_nat_mul, Real.exp_le_exp]
    have h1 : c * (m : ℝ) ≤ lam m := hgrowth m
    have h2 : t * (c * (m : ℝ)) ≤ t * lam m :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
    have heq : (m : ℝ) * -(t * c) = -(t * (c * (m:ℝ))) := by ring
    rw [heq]; linarith
  have hsummable : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_lt_one (le_of_lt hr_pos) hr_lt_one
  calc ∑ m : Fin N, Real.exp (-(t * lam m))
      ≤ ∑ m : Fin N, r ^ (m : ℕ) := by
        apply Finset.sum_le_sum; intro m _; exact hterm m
    _ = ∑ m ∈ Finset.range N, r ^ m := by
        rw [Finset.sum_range fun m => r ^ m]
    _ ≤ ∑' m : ℕ, r ^ m := hsummable.sum_le_tsum _ (fun i _ => le_of_lt (pow_pos hr_pos i))
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one (le_of_lt hr_pos) hr_lt_one

#print axioms sum_exp_neg_le_geometric
end
end RHFormalization
