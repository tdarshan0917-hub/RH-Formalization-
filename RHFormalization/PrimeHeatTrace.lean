import RHFormalization.PrimeNativeStageNonneg
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Brick 1: the heat-semigroup trace of the prime operator
`Tr(e^{-t H_α}) = ∑_k exp(-t (μ_k + w_k + M))`.
`NormedSpace.exp` infers its field from the element's type — no field argument.
-/

namespace RHFormalization
noncomputable section
open Matrix Complex

variable {N : ℕ}

/-- The generator matrix `-t · H_α`. -/
noncomputable def primeHeatGen (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (-(t : ℂ)) • (perturbedMatrix μ (primePotential w) + (M : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))

theorem primeHeatGen_eq_diagonal (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) (t : ℝ) :
    primeHeatGen μ w M t
      = Matrix.diagonal (fun k => (-(t : ℂ)) * ((μ k + w k + M : ℝ) : ℂ)) := by
  unfold primeHeatGen
  rw [primeOpMatrix_eq_diagonal, ← Matrix.diagonal_smul]
  rfl

/-- **The heat trace** `Tr(e^{-t H_α}) = ∑_k exp(-t (μ_k + w_k + M))`. -/
noncomputable def primeHeatTrace (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) (t : ℝ) : ℂ :=
  ∑ k, NormedSpace.exp ((-(t : ℂ)) * ((μ k + w k + M : ℝ) : ℂ))

/-- **Brick 1**: trace of the genuine heat semigroup `e^{-t H_α}` of the prime
operator equals the explicit spectral sum `∑_k exp(-t (μ_k + w_k + M))`. -/
theorem primeHeatTrace_eq_trace_exp (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) (t : ℝ) :
    (NormedSpace.exp (primeHeatGen μ w M t)).trace = primeHeatTrace μ w M t := by
  rw [primeHeatGen_eq_diagonal, Matrix.exp_diagonal, Matrix.trace_diagonal]
  unfold primeHeatTrace
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact Pi.coe_exp _ k

#print axioms primeHeatTrace_eq_trace_exp
end
end RHFormalization
