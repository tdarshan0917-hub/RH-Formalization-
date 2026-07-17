-- SENTINEL: decoded-paired-order1-same-mixed-v2
import RHFormalization.DecodedPairedOrder1Package
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- Same-channel part of the decoded paired order-one package. -/
noncomputable def decodedPairedOrder1SameChannel
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u : ℝ) : ℝ :=
  (2 / L) *
    ∑ k ∈ qs,
      w k *
        ∑ q ∈ qs,
          if q = k then
            w q *
              decodedPairedDuhamel1Channel
                (N := N) δ q L t u (ppDecode k).center
          else 0

/-- Mixed-channel part: inner and outer arithmetic labels are distinct. -/
noncomputable def decodedPairedOrder1MixedChannel
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u : ℝ) : ℝ :=
  (2 / L) *
    ∑ k ∈ qs,
      w k *
        ∑ q ∈ qs,
          if q ≠ k then
            w q *
              decodedPairedDuhamel1Channel
                (N := N) δ q L t u (ppDecode k).center
          else 0

/-- Exact ONE-STEP word sorting at order one:
the double arithmetic sum is the same-channel sector plus the mixed sector. -/
theorem decodedPairedOrder1DoubleSum_eq_same_add_mixed
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u : ℝ) :
    decodedPairedOrder1DoubleSum
        (N := N) δ qs w L t u
      =
    decodedPairedOrder1SameChannel
        (N := N) δ qs w L t u
      +
    decodedPairedOrder1MixedChannel
        (N := N) δ qs w L t u := by
  unfold decodedPairedOrder1DoubleSum
    decodedPairedOrder1SameChannel
    decodedPairedOrder1MixedChannel

  rw [← mul_add]
  congr 1

  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk

  rw [← mul_add]
  congr 1

  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq

  by_cases h : q = k
  · simp [h]
  · simp [h]

/-- Package-level form of the same/mixed split. -/
theorem decodedPairedOrder1Package_eq_same_add_mixed
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t u : ℝ) :
    decodedPairedOrder1Package
        (N := N) δ qs w L t u
      =
    decodedPairedOrder1SameChannel
        (N := N) δ qs w L t u
      +
    decodedPairedOrder1MixedChannel
        (N := N) δ qs w L t u := by
  rw [decodedPairedOrder1Package_eq_doubleSum]
  exact decodedPairedOrder1DoubleSum_eq_same_add_mixed
    (N := N) δ qs w L t u

#print axioms decodedPairedOrder1SameChannel
#print axioms decodedPairedOrder1MixedChannel
#print axioms decodedPairedOrder1DoubleSum_eq_same_add_mixed
#print axioms decodedPairedOrder1Package_eq_same_add_mixed

end

end RHFormalization
