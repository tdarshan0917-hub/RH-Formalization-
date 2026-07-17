-- SENTINEL: decoded-paired-duhamel1-expansion-v2
import RHFormalization.DecodedGalerkinPairedSandwichSplit
import RHFormalization.GalerkinFreeHeatDiagonal
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The decoded paired order-one term as an explicit two-mode sum.

This exposes the decoded potential matrix element between the free heat
weights and the displacement matrix, ready for expansion into arithmetic
channels. -/
theorem decodedPairedDuhamel1Integrand_eq_index_sum
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L t u a : ℝ) :
    decodedPairedDuhamel1Integrand
        (N := N) δ qs w L t u a
      =
    ∑ i : Fin N, ∑ j : Fin N,
      heatWeight (N := N) L (t - u) i
        * decodedGalerkinV
            (N := N) δ qs w L i j
        * heatWeight (N := N) L u j
        * galerkinT (N := N) L a j i := by
  unfold decodedPairedDuhamel1Integrand
  rw [galerkinFreeHeat_eq_diagonal]
  simp only [
    Matrix.trace,
    Matrix.diag,
    Matrix.mul_apply,
    Matrix.diagonal_apply,
    Finset.mul_sum,
    Finset.sum_mul
  ]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Finset.sum_ite_eq', Finset.mem_univ] <;> ring

#print axioms decodedPairedDuhamel1Integrand_eq_index_sum

end

end RHFormalization
