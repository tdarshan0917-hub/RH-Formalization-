-- SENTINEL: decoded-paired-duhamel1-bump-sum-v1
import RHFormalization.DecodedPairedDuhamel1Expansion
import RHFormalization.DecodedPrimePotentialBumpSplit
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Expand the decoded paired order-one integrand into its physical
prime-power bump contributions, before commuting the finite sums. -/
theorem decodedPairedDuhamel1Integrand_eq_bump_sum
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L t u a : ℝ) :
    decodedPairedDuhamel1Integrand
        (N := N) δ qs w L t u a
      =
    ∑ i : Fin N, ∑ j : Fin N,
      heatWeight (N := N) L (t - u) i
        *
        ((2 / L) *
          ∑ q ∈ qs,
            w q *
              decodedBumpMatrixElement
                δ q L
                ((i : ℕ) + 1)
                ((j : ℕ) + 1))
        *
        heatWeight (N := N) L u j
        *
        galerkinT (N := N) L a j i := by
  rw [decodedPairedDuhamel1Integrand_eq_index_sum]

  apply Finset.sum_congr rfl
  intro i _

  apply Finset.sum_congr rfl
  intro j _

  have hV :
      decodedGalerkinV
          (N := N) δ qs w L i j
        =
      (2 / L) *
        ∑ q ∈ qs,
          w q *
            decodedBumpMatrixElement
              δ q L
              ((i : ℕ) + 1)
              ((j : ℕ) + 1) := by
    unfold decodedGalerkinV
    rw [decodedVmatrixElement_eq_sum_bumps]

  rw [hV]

#print axioms decodedPairedDuhamel1Integrand_eq_bump_sum

end

end RHFormalization
