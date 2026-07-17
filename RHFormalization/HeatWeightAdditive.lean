import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- heatWeight is additive in time: e^{-aλ}·e^{-bλ} = e^{-(a+b)λ}. -/
theorem heatWeight_mul (L a b : ℝ) (i : Fin N) :
    heatWeight (N := N) L a i * heatWeight (N := N) L b i
      = heatWeight (N := N) L (a + b) i := by
  unfold heatWeight
  rw [← Real.exp_add]
  congr 1
  ring

/-- Product of two diagonal heat matrices is the diagonal at the summed time. -/
theorem diagonal_heatWeight_mul (L a b : ℝ) :
    (Matrix.diagonal (heatWeight (N := N) L a))
      * (Matrix.diagonal (heatWeight (N := N) L b))
      = Matrix.diagonal (heatWeight (N := N) L (a + b)) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact heatWeight_mul L a b i

#print axioms heatWeight_mul
#print axioms diagonal_heatWeight_mul

end

end RHFormalization
