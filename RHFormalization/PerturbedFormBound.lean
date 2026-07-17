import RHFormalization.FinitePerturbedSpectrum
import RHFormalization.GroundStateFormMonotone

/-!
# Ground-state A.GROWTH, step 1: the perturbed form bound

For the perturbed operator `H_N = D + V`, the quadratic form satisfies
`re⟨pertOp V x, x⟩ ≥ -‖V_op‖‖x‖²` (Cauchy–Schwarz), and `perturbedOp` splits as
`freeDiagOp + pertOp`. Together these give the form lower bound that is the heart
of A.GROWTH at the ground state.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Complex RCLike
open scoped InnerProductSpace

variable {N : ℕ}

/-- The free diagonal operator on Euclidean space. -/
noncomputable def freeDiagOp (μ : Fin N → ℝ) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanLin (freeDiag μ)

/-- The perturbation operator on Euclidean space. -/
noncomputable def pertOp (V : Matrix (Fin N) (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanLin V

/-- `perturbedOp` splits as `freeDiagOp + pertOp`. -/
theorem perturbedOp_eq_add (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) :
    perturbedOp μ V = freeDiagOp μ + pertOp V := by
  unfold perturbedOp freeDiagOp pertOp perturbedMatrix
  exact map_add Matrix.toEuclideanLin (freeDiag μ) V

/-- Cauchy–Schwarz form lower bound for the perturbation:
`∃ M ≥ 0, ∀ x, -M‖x‖² ≤ re⟨pertOp V x, x⟩`. -/
theorem pertOp_form_lower_bound (V : Matrix (Fin N) (Fin N) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : EuclideanSpace ℂ (Fin N),
      -M * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ ((pertOp V) x) x) := by
  classical
  let Vc : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
    LinearMap.toContinuousLinearMap (pertOp V)
  refine ⟨‖Vc‖, norm_nonneg _, ?_⟩
  intro x
  have hVx : ‖((pertOp V) x)‖ ≤ ‖Vc‖ * ‖x‖ := by
    have hrw : ((pertOp V) x) = Vc x := rfl
    rw [hrw]; exact Vc.le_opNorm x
  have hlow : -(‖((pertOp V) x)‖ * ‖x‖) ≤ RCLike.re (inner ℂ ((pertOp V) x) x) := by
    have hneg := re_inner_le_norm (𝕜 := ℂ) (-((pertOp V) x)) x
    simp only [inner_neg_left, map_neg, norm_neg] at hneg
    linarith [hneg]
  have hstep : -(‖Vc‖ * ‖x‖ * ‖x‖) ≤ -(‖((pertOp V) x)‖ * ‖x‖) := by
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right hVx (norm_nonneg _)
  have : -(‖Vc‖ * ‖x‖ * ‖x‖) ≤ RCLike.re (inner ℂ ((pertOp V) x) x) :=
    le_trans hstep hlow
  have hsq : ‖Vc‖ * ‖x‖ * ‖x‖ = ‖Vc‖ * ‖x‖ ^ 2 := by ring
  rw [hsq] at this
  linarith [this]

#print axioms perturbedOp_eq_add
#print axioms pertOp_form_lower_bound

end

end RHFormalization
