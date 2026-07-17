import RHFormalization.PerturbedFormBound

/-!
# Ground-state A.GROWTH (form level)

The perturbed operator `H_N = D + V` satisfies the quadratic-form lower bound
`re⟨D x, x⟩ - ‖V_op‖·‖x‖² ≤ re⟨H_N x, x⟩` for all x.

This is the operator-theoretic core of A.GROWTH at the ground state: the
perturbed quadratic form sits at most ‖V‖ below the free form, everywhere.
The further identification of the Rayleigh infimum with the smallest eigenvalue
(`hasEigenvalue_iInf` + ciInf monotonicity) is order-theoretic plumbing for a
later step; the form bound itself is complete and axiom-clean here.

(Stated as a bare inequality rather than via the `FormLowerBound` predicate,
which is typed for continuous linear maps `→L`; `perturbedOp`/`freeDiagOp` are
bare `LinearMap`s `→ₗ`. The mathematical content is identical.)
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Complex RCLike
open scoped InnerProductSpace

variable {N : ℕ}

/-- The perturbation's operator-norm, the A.GROWTH ground-state drop constant. -/
noncomputable def growthDrop (V : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (pertOp V)‖

theorem growthDrop_nonneg (V : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ growthDrop V :=
  norm_nonneg _

/-- **Ground-state A.GROWTH, form level.** The perturbed operator `H_N = D + V`
has quadratic form at most `growthDrop V = ‖V_op‖` below the free form:
`re⟨D x, x⟩ - ‖V_op‖·‖x‖² ≤ re⟨H_N x, x⟩` for all x. -/
theorem perturbedOp_formLowerBound (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ (freeDiagOp μ x) x) - growthDrop V * ‖x‖ ^ 2
      ≤ RCLike.re (inner ℂ (perturbedOp μ V x) x) := by
  have hsplit : perturbedOp μ V x = freeDiagOp μ x + pertOp V x := by
    rw [perturbedOp_eq_add]; rfl
  have hre : RCLike.re (inner ℂ (perturbedOp μ V x) x)
      = RCLike.re (inner ℂ (freeDiagOp μ x) x)
        + RCLike.re (inner ℂ (pertOp V x) x) := by
    rw [hsplit, inner_add_left, map_add]
  have hpert : -(growthDrop V) * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (pertOp V x) x) := by
    have hVx : ‖pertOp V x‖ ≤ growthDrop V * ‖x‖ := by
      unfold growthDrop
      exact (LinearMap.toContinuousLinearMap (pertOp V)).le_opNorm x
    have hlow : -(‖pertOp V x‖ * ‖x‖) ≤ RCLike.re (inner ℂ (pertOp V x) x) := by
      have hneg := re_inner_le_norm (𝕜 := ℂ) (-(pertOp V x)) x
      simp only [inner_neg_left, map_neg, norm_neg] at hneg
      linarith [hneg]
    have hstep : -(growthDrop V * ‖x‖ * ‖x‖) ≤ -(‖pertOp V x‖ * ‖x‖) := by
      apply neg_le_neg
      exact mul_le_mul_of_nonneg_right hVx (norm_nonneg _)
    have hchain := le_trans hstep hlow
    have hsq : growthDrop V * ‖x‖ * ‖x‖ = growthDrop V * ‖x‖ ^ 2 := by ring
    rw [hsq] at hchain
    linarith [hchain]
  rw [hre]
  linarith [hpert]

#print axioms perturbedOp_formLowerBound

end

end RHFormalization
