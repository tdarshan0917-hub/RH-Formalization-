import RHFormalization.HeatSumSqrtBound
import RHFormalization.PrimeDuhamel2IntegrandBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real
open scoped BigOperators

variable {N : ℕ}

/-- **Brick 3a (heat-sum sqrt bound).** For eigenvalues bounded below by the quadratic
`((n+1)π/L)²` (shifted by the potential bound `M`), the heat sum is `O(t^{-1/2})`:
`∑_n e^{-t·λ_n} ≤ e^{tM}·√(π/(t(π/L)²))/2`. This is the reusable cutoff-uniform core. -/
theorem prime_heat_sum_sqrt_bound
    (L : ℝ) (hL : 0 < L) (M : ℝ) (t : ℝ) (ht : 0 < t)
    (lam : Fin N → ℝ)
    (hlam : ∀ n : Fin N, ((((n : ℝ) + 1) * Real.pi / L) ^ 2) - M ≤ lam n) :
    ∑ n : Fin N, Real.exp (-t * lam n)
      ≤ Real.exp (t * M) * (Real.sqrt (Real.pi / (t * (Real.pi / L) ^ 2)) / 2) := by
  -- Step 1: e^{-t·lam n} ≤ e^{tM}·e^{-t·((n+1)π/L)²}
  have hstep : ∀ n : Fin N,
      Real.exp (-t * lam n)
        ≤ Real.exp (t * M) * Real.exp (-(t * (Real.pi / L) ^ 2) * ((n : ℝ) + 1) ^ 2) := by
    intro n
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := hlam n
    have hpi : (((n : ℝ) + 1) * Real.pi / L) ^ 2 = (Real.pi / L) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      ring
    rw [hpi] at h
    -- from h: (π/L)²(n+1)² - M ≤ lam n; multiply by -t (t>0): -t·lam n ≤ tM - t(π/L)²(n+1)²
    have hmul : -t * lam n ≤ -t * ((Real.pi / L) ^ 2 * ((n : ℝ) + 1) ^ 2 - M) := by
      apply mul_le_mul_of_nonpos_left h
      linarith [ht.le]
    nlinarith [hmul]
  -- Step 2: sum the bound
  calc ∑ n : Fin N, Real.exp (-t * lam n)
      ≤ ∑ n : Fin N, Real.exp (t * M)
          * Real.exp (-(t * (Real.pi / L) ^ 2) * ((n : ℝ) + 1) ^ 2) :=
        Finset.sum_le_sum (fun n _ => hstep n)
    _ = Real.exp (t * M)
          * ∑ n : Fin N, Real.exp (-(t * (Real.pi / L) ^ 2) * ((n : ℝ) + 1) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (t * M) * (Real.sqrt (Real.pi / (t * (Real.pi / L) ^ 2)) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        have hb : 0 < t * (Real.pi / L) ^ 2 := by positivity
        exact sum_exp_neg_sq_le_gaussian (t * (Real.pi / L) ^ 2) hb

#print axioms prime_heat_sum_sqrt_bound

end
end RHFormalization
