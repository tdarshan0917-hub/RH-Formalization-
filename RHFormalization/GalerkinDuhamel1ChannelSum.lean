import RHFormalization.GalerkinDuhamel1BumpSum
import Mathlib

/-!
# Galerkin first-order Duhamel channel sum

This rewrites the order-1 Galerkin Duhamel term as a sum over prime/bump
channels. This is the next algebraic step toward the D.SHIFT-CHANNEL
spike-identification.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The first-order contribution of one bump/prime channel `q`. -/
noncomputable def duhamel1Channel
    (δ : ℝ) (q : ℕ) (L : ℝ) (t u : ℝ) : ℝ :=
  ∑ m : Fin N,
    heatWeight (N := N) L (t - u) m
      * bumpMatrixElement δ q L (m + 1) (m + 1)
      * heatWeight (N := N) L u m

/--
Order-1 Galerkin Duhamel term as a sum over prime/bump channels.

This isolates the channel kernel that later must be identified with the
B-side shifted heat/spike kernel.
-/
theorem duhamel1Integrand_eq_channel_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u =
      (2 / L) * ∑ q ∈ qs, w q * duhamel1Channel (N := N) δ q L t u := by
  rw [duhamel1Integrand_eq_bump_sum]
  unfold duhamel1Channel
  have hpull : (∑ m : Fin N,
      heatWeight (N := N) L (t - u) m
        * ((2 / L) * ∑ q ∈ qs,
              w q * bumpMatrixElement δ q L (m + 1) (m + 1))
        * heatWeight (N := N) L u m)
      = (2 / L) * ∑ m : Fin N,
          heatWeight (N := N) L (t - u) m
            * (∑ q ∈ qs,
                  w q * bumpMatrixElement δ q L (m + 1) (m + 1))
            * heatWeight (N := N) L u m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hpull]
  congr 1
  calc
    (∑ m : Fin N,
        heatWeight (N := N) L (t - u) m
          * (∑ q ∈ qs,
                w q * bumpMatrixElement δ q L (m + 1) (m + 1))
          * heatWeight (N := N) L u m)
        =
      ∑ m : Fin N, ∑ q ∈ qs,
        w q *
          (heatWeight (N := N) L (t - u) m
            * bumpMatrixElement δ q L (m + 1) (m + 1)
            * heatWeight (N := N) L u m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        ring
    _ =
      ∑ q ∈ qs, ∑ m : Fin N,
        w q *
          (heatWeight (N := N) L (t - u) m
            * bumpMatrixElement δ q L (m + 1) (m + 1)
            * heatWeight (N := N) L u m) := by
        rw [Finset.sum_comm]
    _ =
      ∑ q ∈ qs, w q *
        ∑ m : Fin N,
          heatWeight (N := N) L (t - u) m
            * bumpMatrixElement δ q L (m + 1) (m + 1)
            * heatWeight (N := N) L u m := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]

#print axioms duhamel1Channel
#print axioms duhamel1Integrand_eq_channel_sum

end
end RHFormalization
