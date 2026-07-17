-- SENTINEL: decoded-paired-same-channel-collapse-v1
import RHFormalization.DecodedPairedOrder1SameMixedSplit
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- The same-channel sector collapses to one sum:
each outer displacement label is paired with the identical potential label. -/
theorem decodedPairedOrder1SameChannel_eq_singleSum
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L t u : ℝ) :
    decodedPairedOrder1SameChannel
        (N := N) δ qs w L t u
      =
    (2 / L) *
      ∑ k ∈ qs,
        (w k) ^ 2 *
          decodedPairedDuhamel1Channel
            (N := N) δ k L t u (ppDecode k).center := by
  unfold decodedPairedOrder1SameChannel

  congr 1

  apply Finset.sum_congr rfl
  intro k hk

  have hinner :
      (∑ q ∈ qs,
        if q = k then
          w q *
            decodedPairedDuhamel1Channel
              (N := N) δ q L t u (ppDecode k).center
        else 0)
        =
      w k *
        decodedPairedDuhamel1Channel
          (N := N) δ k L t u (ppDecode k).center := by
    simp [hk]

  rw [hinner]
  ring

#print axioms decodedPairedOrder1SameChannel_eq_singleSum

end

end RHFormalization
