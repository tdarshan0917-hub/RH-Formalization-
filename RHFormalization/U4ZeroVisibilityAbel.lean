import RHFormalization.DBFFAbelTransfer
import RHFormalization.DBFFStarObject
import RHFormalization.ShiftedLaplaceBranchIdentity
import RHFormalization.ShiftedLaplaceModelPP
import RHFormalization.PrimePowerSumConvergence
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Finset
open scoped BigOperators

/--
Complex version of the existing Abel norm transfer.

No arithmetic input: bounded complex partial sums imply the usual
finite weighted Abel bound.
-/
theorem abel_transfer_norm_bound_complex
    (a w : ℕ → ℂ) (C : ℝ)
    (hA : ∀ n : ℕ, ‖∑ k ∈ range (n+1), a k‖ ≤ C)
    (n : ℕ) :
    ‖∑ k ∈ range (n+1), a k * w k‖
      ≤ C * (‖w n‖ + ∑ k ∈ range n, ‖w k - w (k+1)‖) := by
  rw [abel_partial_sum_c a w n]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hA 0)
  calc
    ‖(∑ k ∈ range (n+1), a k) * w n
        + ∑ k ∈ range n,
            (∑ j ∈ range (k+1), a j) * (w k - w (k+1))‖
        ≤ ‖(∑ k ∈ range (n+1), a k) * w n‖
          + ‖∑ k ∈ range n,
              (∑ j ∈ range (k+1), a j) * (w k - w (k+1))‖ :=
            norm_add_le _ _
    _ ≤ C * ‖w n‖
          + ∑ k ∈ range n, C * ‖w k - w (k+1)‖ := by
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _)
        · refine le_trans (norm_sum_le _ _) ?_
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _)
    _ = C * (‖w n‖ + ∑ k ∈ range n, ‖w k - w (k+1)‖) := by
        rw [mul_add, Finset.mul_sum]


/--
Every integer cutoff `M ≥ 2` is realized exactly by the admissible schedule
at stage `n = M^2 - 2`.
-/
theorem admR_square_cutoff_realizes_nat
    (M : ℕ) (hM : 2 ≤ M) :
    ⌊Real.exp (admR (M^2 - 2))⌋₊ = M := by
  rw [exp_admR]
  have hsq : 2 ≤ M^2 := by
    nlinarith
  have hnat : M^2 - 2 + 2 = M^2 :=
    Nat.sub_add_cancel hsq
  have harg :
      (((M^2 - 2 : ℕ) : ℝ) + 2) = (M : ℝ)^2 := by
    exact_mod_cast hnat
  rw [harg, Real.sqrt_sq_eq_abs]
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  rw [abs_of_nonneg hM0, Nat.floor_natCast]

#print axioms admR_square_cutoff_realizes_nat

/--
The concrete centered von-Mangoldt discrepancy at integer cutoff `M`
and complex exponent `ρ`.
-/
noncomputable def u4WitnessDiscrepancy
    (M : ℕ) (ρ : ℂ) : ℂ :=
  (∑ k ∈ Finset.Ioc 0 M,
      LSeries.term
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        ρ k)
    - mainTermIntegral (M^2 - 2) (polePoint ρ)
    - 1 / (1 - ρ)

/--
At a right-half zero coordinate, the actual finite `starObject`
specializes EXACTLY to the witness discrepancy at cutoff `M`.

No estimate and no continuation theorem are used here.
-/
theorem starObject_square_stage_eq_witnessDiscrepancy
    (M : ℕ) (ρ : ℂ)
    (hM : 2 ≤ M)
    (hρ : (1/2 : ℝ) < ρ.re) :
    starObject (M^2 - 2) (polePoint ρ)
      = u4WitnessDiscrepancy M ρ := by
  unfold starObject u4WitnessDiscrepancy
  rw [admR_square_cutoff_realizes_nat M hM]
  rw [sqrt_polePoint_eq_of_re_gt hρ]
  have hphi :
      ρ - (1/2 : ℂ) + (1/2 : ℂ) = ρ := by
    ring
  have hden :
      (1/2 : ℂ) - (ρ - (1/2 : ℂ)) = 1 - ρ := by
    ring
  rw [hphi, hden]

#print axioms u4WitnessDiscrepancy
#print axioms starObject_square_stage_eq_witnessDiscrepancy



#print axioms abel_transfer_norm_bound_complex

end

end RHFormalization
