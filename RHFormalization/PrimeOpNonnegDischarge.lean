import RHFormalization.PrimeNativeStageNonneg
import Mathlib

/-!
# Discharge of hnn: prime operator nonnegativity from the global shift M.

primeOpCLM_form_eq_sum gives re<y, H y> = sum_k (mu_k + w_k + M) |y_k|^2.
Therefore if every coefficient mu_k + w_k + M >= 0 (i.e. M >= -(mu_k + w_k) for all k,
the manuscript's single global shift, p12), then re<y, H y> >= 0 for all y.

This DISCHARGES the hnn hypothesis carried everywhere: it is now PROVEN from the
shift condition, which is a choice of M, not an assumption about the operator.
The operator is diagonal, so nonnegativity is just nonneg diagonal entries.
-/

namespace RHFormalization
noncomputable section
open RCLike
open scoped BigOperators

variable {N : ℕ}

/-- **hnn discharged.** If the global shift makes every diagonal coefficient nonnegative,
the prime operator is nonnegative — no operator assumption, just `M` large enough. -/
theorem primeOpCLM_nonneg_of_shift
    (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ)
    (hM : ∀ k, 0 ≤ μ k + w k + M) :
    ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y (primeOpCLM μ w M y)) := by
  intro y
  rw [primeOpCLM_form_eq_sum]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hM k) (sq_nonneg _)

/-- The shift condition is always satisfiable: pick `M` at least `max_k (-(mu_k + w_k))`.
Concretely `M := sup over k of -(mu k + w k)` (or any larger value) works. -/
theorem exists_shift_making_nonneg
    (μ : Fin N → ℝ) (w : Fin N → ℝ) :
    ∃ M : ℝ, ∀ k, 0 ≤ μ k + w k + M := by
  rcases Finset.exists_le (Finset.univ.image (fun k => -(μ k + w k))) with ⟨M, hM⟩
  refine ⟨M, fun k => ?_⟩
  have : -(μ k + w k) ≤ M := hM _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  linarith

#print axioms primeOpCLM_nonneg_of_shift
#print axioms exists_shift_making_nonneg

end
end RHFormalization
