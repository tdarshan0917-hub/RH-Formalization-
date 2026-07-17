/-
GalerkinOpNonnegDischarge.lean

hnn discharged for the GENUINE galerkin operator: with global shift
M >= ||V||_op - min mu, the operator H0 + galerkinV + M*I is nonnegative.
Route: free-diagonal form sum + perturbedOp form lower bound (Cauchy-Schwarz,
banked). The unconditional genuine stage follows: zero live hypotheses.
-/
import RHFormalization.GalerkinOperatorDFiniteStage
import Mathlib

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike Complex

variable {N : ℕ}

/-- Free-diagonal quadratic form as a sum. -/
theorem freeDiagOp_form_eq_sum (μ : Fin N → ℝ) (y : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ y (freeDiagOp μ y)) = ∑ k, μ k * ‖y k‖ ^ 2 := by
  unfold freeDiagOp freeDiag
  rw [PiLp.inner_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have happ : (Matrix.toEuclideanLin
      (Matrix.diagonal (fun j => ((μ j : ℝ) : ℂ))) y) k
      = ((μ k : ℝ) : ℂ) * y k := by
    show ((Matrix.diagonal (fun j => ((μ j : ℝ) : ℂ))) *ᵥ (y : Fin N → ℂ)) k
        = ((μ k : ℝ) : ℂ) * y k
    rw [Matrix.mulVec_diagonal]
  rw [RCLike.inner_apply, happ]
  have hconj : y k * (starRingEnd ℂ) (y k) = ((‖y k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hfactor : ((μ k : ℝ) : ℂ) * y k * (starRingEnd ℂ) (y k)
      = ((μ k : ℝ) : ℂ) * ((‖y k‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, hconj]
  rw [hfactor, ← Complex.ofReal_mul]
  norm_cast

/-- The galerkin operator CLM form splits as perturbed form + M‖y‖². -/
theorem galerkinOpCLM_form_split
    (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (y : EuclideanSpace ℂ (Fin N)) :
    RCLike.re (inner ℂ y (galerkinOpCLM μ δ qs w L M y))
      = RCLike.re (inner ℂ y (perturbedOp μ (galerkinVC (N := N) δ qs w L) y))
        + M * ‖y‖ ^ 2 := by
  have happly : galerkinOpCLM μ δ qs w L M y
      = perturbedOp μ (galerkinVC (N := N) δ qs w L) y + (M : ℂ) • y := by
    show (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N)
        (perturbedMatrix μ (galerkinVC (N := N) δ qs w L)
          + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))) y
      = Matrix.toEuclideanLin (perturbedMatrix μ (galerkinVC (N := N) δ qs w L)) y
        + (M : ℂ) • y
    rw [_root_.map_add, _root_.map_smul, map_one]
    rfl
  rw [happly, inner_add_right, _root_.map_add, inner_smul_right]
  have hre : RCLike.re ((M : ℂ) * inner ℂ y y) = M * ‖y‖ ^ 2 := by
    have h1 : inner ℂ y y = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      first | rfl | norm_cast | norm_num | simp
    rw [h1, ← Complex.ofReal_mul]
    norm_cast
  rw [hre]

/-- **hnn discharged (genuine operator).** With shift `M ≥ ‖V‖ − μ_k` for all k,
the galerkin operator is nonnegative. -/
theorem galerkinOpCLM_nonneg_of_shift
    (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (hM : ∀ k, growthDrop (galerkinVC (N := N) δ qs w L) ≤ μ k + M) :
    ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y (galerkinOpCLM μ δ qs w L M y)) := by
  intro y
  rw [galerkinOpCLM_form_split]
  have hlow := perturbedOp_formLowerBound μ (galerkinVC (N := N) δ qs w L) y
  have hflip1 := re_inner_comm (perturbedOp μ (galerkinVC (N := N) δ qs w L)) y
  have hflip2 := re_inner_comm (freeDiagOp μ) y
  rw [hflip1, hflip2] at hlow
  have hfree : RCLike.re (inner ℂ y (freeDiagOp μ y)) = ∑ k, μ k * ‖y k‖ ^ 2 :=
    freeDiagOp_form_eq_sum μ y
  have hnormsum : ‖y‖ ^ 2 = ∑ k, ‖y k‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
  have hterm : 0 ≤ ∑ k,
      (μ k - growthDrop (galerkinVC (N := N) δ qs w L) + M) * ‖y k‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (by linarith [hM k]) (sq_nonneg _)
  have hexpand : ∑ k,
      (μ k - growthDrop (galerkinVC (N := N) δ qs w L) + M) * ‖y k‖ ^ 2
      = (∑ k, μ k * ‖y k‖ ^ 2)
        - growthDrop (galerkinVC (N := N) δ qs w L) * (∑ k, ‖y k‖ ^ 2)
        + M * (∑ k, ‖y k‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hfree, hnormsum] at hlow
  rw [hnormsum]
  linarith [hlow, hterm, hexpand]

/-- The shift condition is always satisfiable. -/
theorem exists_shift_making_galerkin_nonneg
    (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    ∃ M : ℝ, ∀ k, growthDrop (galerkinVC (N := N) δ qs w L) ≤ μ k + M := by
  rcases Finset.exists_le
    (Finset.univ.image
      (fun k => growthDrop (galerkinVC (N := N) δ qs w L) - μ k)) with ⟨M, hM⟩
  refine ⟨M, fun k => ?_⟩
  have := hM _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  linarith

/-- **Unconditional genuine stage**: hnn is PROVEN inside from the shift. -/
noncomputable def galerkinOperatorDFiniteStage_ofShift
    (n : ℕ) (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (hshift : ∀ k, growthDrop (galerkinVC (N := N) δ qs w L) ≤ μ k + M) :
    DFiniteStage :=
  galerkinOperatorDFiniteStage n μ δ qs w L M
    (galerkinOpCLM_nonneg_of_shift μ δ qs w L M hshift)

#print axioms freeDiagOp_form_eq_sum
#print axioms galerkinOpCLM_form_split
#print axioms galerkinOpCLM_nonneg_of_shift
#print axioms exists_shift_making_galerkin_nonneg
#print axioms galerkinOperatorDFiniteStage_ofShift

end
end RHFormalization
