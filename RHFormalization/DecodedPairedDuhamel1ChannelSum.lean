-- SENTINEL: decoded-paired-duhamel1-channel-sum-v1
import RHFormalization.DecodedPairedDuhamel1BumpSum
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- The contribution of one decoded physical prime-power channel to the
paired order-one Duhamel term. -/
noncomputable def decodedPairedDuhamel1Channel
    (δ : ℝ)
    (q : ℕ)
    (L t u a : ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    heatWeight (N := N) L (t - u) i
      * decodedBumpMatrixElement
          δ q L
          ((i : ℕ) + 1)
          ((j : ℕ) + 1)
      * heatWeight (N := N) L u j
      * galerkinT (N := N) L a j i

/-- The decoded paired order-one term is exactly the weighted finite sum
over physical prime-power channels. -/
theorem decodedPairedDuhamel1Integrand_eq_channel_sum
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L t u a : ℝ) :
    decodedPairedDuhamel1Integrand
        (N := N) δ qs w L t u a
      =
    (2 / L) *
      ∑ q ∈ qs,
        w q *
          decodedPairedDuhamel1Channel
            (N := N) δ q L t u a := by
  rw [decodedPairedDuhamel1Integrand_eq_bump_sum]
  unfold decodedPairedDuhamel1Channel

  have hpoint :
      ∀ i : Fin N, ∀ j : Fin N,
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
            galerkinT (N := N) L a j i
          =
        ∑ q ∈ qs,
          (2 / L) * w q *
            (heatWeight (N := N) L (t - u) i
              * decodedBumpMatrixElement
                  δ q L
                  ((i : ℕ) + 1)
                  ((j : ℕ) + 1)
              * heatWeight (N := N) L u j
              * galerkinT (N := N) L a j i) := by
    intro i j
    rw [show
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
          galerkinT (N := N) L a j i
        =
      (2 / L) *
        (∑ q ∈ qs,
          w q *
            decodedBumpMatrixElement
              δ q L
              ((i : ℕ) + 1)
              ((j : ℕ) + 1))
        *
        (heatWeight (N := N) L (t - u) i
          * heatWeight (N := N) L u j
          * galerkinT (N := N) L a j i) by
            ring]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring

  calc
    (∑ i : Fin N, ∑ j : Fin N,
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
          galerkinT (N := N) L a j i)
        =
      ∑ i : Fin N, ∑ j : Fin N, ∑ q ∈ qs,
        (2 / L) * w q *
          (heatWeight (N := N) L (t - u) i
            * decodedBumpMatrixElement
                δ q L
                ((i : ℕ) + 1)
                ((j : ℕ) + 1)
            * heatWeight (N := N) L u j
            * galerkinT (N := N) L a j i) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hpoint i j

    _ =
      ∑ i : Fin N, ∑ q ∈ qs, ∑ j : Fin N,
        (2 / L) * w q *
          (heatWeight (N := N) L (t - u) i
            * decodedBumpMatrixElement
                δ q L
                ((i : ℕ) + 1)
                ((j : ℕ) + 1)
            * heatWeight (N := N) L u j
            * galerkinT (N := N) L a j i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]

    _ =
      ∑ q ∈ qs, ∑ i : Fin N, ∑ j : Fin N,
        (2 / L) * w q *
          (heatWeight (N := N) L (t - u) i
            * decodedBumpMatrixElement
                δ q L
                ((i : ℕ) + 1)
                ((j : ℕ) + 1)
            * heatWeight (N := N) L u j
            * galerkinT (N := N) L a j i) := by
          rw [Finset.sum_comm]

    _ =
      ∑ q ∈ qs,
        ((2 / L) * w q) *
          (∑ i : Fin N, ∑ j : Fin N,
            heatWeight (N := N) L (t - u) i
              * decodedBumpMatrixElement
                  δ q L
                  ((i : ℕ) + 1)
                  ((j : ℕ) + 1)
              * heatWeight (N := N) L u j
              * galerkinT (N := N) L a j i) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]

    _ =
      (2 / L) *
        ∑ q ∈ qs,
          w q *
            (∑ i : Fin N, ∑ j : Fin N,
              heatWeight (N := N) L (t - u) i
                * decodedBumpMatrixElement
                    δ q L
                    ((i : ℕ) + 1)
                    ((j : ℕ) + 1)
                * heatWeight (N := N) L u j
                * galerkinT (N := N) L a j i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          ring

#print axioms decodedPairedDuhamel1Channel
#print axioms decodedPairedDuhamel1Integrand_eq_channel_sum

end

end RHFormalization
