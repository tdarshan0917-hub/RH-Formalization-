-- SENTINEL: decoded-paired-order1-package-v1
import RHFormalization.DecodedPairedDuhamel1ChannelSum
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- The decoded paired order-one package, summed over the outer
prime-power displacement channel. -/
noncomputable def decodedPairedOrder1Package
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L t u : ℝ) : ℝ :=
  ∑ k ∈ qs,
    w k *
      decodedPairedDuhamel1Integrand
        (N := N) δ qs w L t u (ppDecode k).center

/-- The explicit double-channel form: outer displacement channel `k`,
inner potential channel `q`. -/
noncomputable def decodedPairedOrder1DoubleSum
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L t u : ℝ) : ℝ :=
  (2 / L) *
    ∑ k ∈ qs,
      w k *
        ∑ q ∈ qs,
          w q *
            decodedPairedDuhamel1Channel
              (N := N) δ q L t u (ppDecode k).center

/-- The paired order-one package is exactly the finite double channel sum.
This is the input for the same-channel versus mixed-channel partition. -/
theorem decodedPairedOrder1Package_eq_doubleSum
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L t u : ℝ) :
    decodedPairedOrder1Package
        (N := N) δ qs w L t u
      =
    decodedPairedOrder1DoubleSum
        (N := N) δ qs w L t u := by
  unfold decodedPairedOrder1Package
    decodedPairedOrder1DoubleSum

  calc
    (∑ k ∈ qs,
      w k *
        decodedPairedDuhamel1Integrand
          (N := N) δ qs w L t u (ppDecode k).center)
      =
    ∑ k ∈ qs,
      w k *
        ((2 / L) *
          ∑ q ∈ qs,
            w q *
              decodedPairedDuhamel1Channel
                (N := N) δ q L t u
                (ppDecode k).center) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [
        decodedPairedDuhamel1Integrand_eq_channel_sum
          (N := N) δ qs w L t u (ppDecode k).center
      ]

    _ =
      (2 / L) *
        ∑ k ∈ qs,
          w k *
            ∑ q ∈ qs,
              w q *
                decodedPairedDuhamel1Channel
                  (N := N) δ q L t u
                  (ppDecode k).center := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

#print axioms decodedPairedOrder1Package
#print axioms decodedPairedOrder1DoubleSum
#print axioms decodedPairedOrder1Package_eq_doubleSum

end

end RHFormalization
