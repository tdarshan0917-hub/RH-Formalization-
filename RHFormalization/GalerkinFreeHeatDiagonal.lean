import RHFormalization.GalerkinFreeHeatDeriv
import RHFormalization.GalerkinMatrices
import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

set_option autoImplicit false
namespace RHFormalization
noncomputable section
open Matrix
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- **Free heat is diagonal heatWeight.** `exp(u•(-K)) = diagonal(heatWeight u)`. -/
theorem galerkinFreeHeat_eq_diagonal (L : ℝ) (u : ℝ) :
    NormedSpace.exp (u • (-(galerkinK (N := N) L)))
      = Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L u m) := by
  have hstep : u • (-(galerkinK (N := N) L))
      = Matrix.diagonal (fun m : Fin N => -(u * galerkinLam L (m : ℕ))) := by
    unfold galerkinK galerkinLam
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.diagonal_apply_eq, mul_comm, mul_neg, neg_mul]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.smul_apply, Matrix.neg_apply]
  rw [hstep, Matrix.exp_diagonal]
  ext i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    -- goal: (NormedSpace.exp (fun m => -(u*galerkinLam L m))) i = heatWeight L u i
    unfold heatWeight
    first
      | rw [Pi.exp_apply, ← Real.exp_eq_exp_ℝ]
      | rw [NormedSpace.exp_pi_apply, ← Real.exp_eq_exp_ℝ]
      | rw [NormedSpace.Pi.exp_apply, ← Real.exp_eq_exp_ℝ]
      | (rw [show (NormedSpace.exp (fun m : Fin N => -(u * galerkinLam L (m : ℕ)))) i
            = NormedSpace.exp (-(u * galerkinLam L (i : ℕ))) from by
          first
            | exact congrFun (NormedSpace.exp_pi _) i
            | exact Pi.exp_def ▸ rfl
            | simp [NormedSpace.exp_eq_tsum]]
         rw [← Real.exp_eq_exp_ℝ])
      | simp [← Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum, Real.exp_eq_tsum]
  · simp [Matrix.diagonal_apply_ne _ h]

#print axioms galerkinFreeHeat_eq_diagonal
