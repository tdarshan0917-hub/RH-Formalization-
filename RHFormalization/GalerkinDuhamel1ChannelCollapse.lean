import RHFormalization.GalerkinDuhamel1ChannelSum
import Mathlib

/-!
# Galerkin first-order channel collapse

Collapses the same-index heat factors in the order-1 Galerkin channel:

  e^{-(t-u)λ_m} · e^{-uλ_m} = e^{-tλ_m}

This turns the order-1 Duhamel channel into the finite heat-kernel bump trace.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Same-index heat weights multiply to the full-time heat weight. -/
theorem heatWeight_mul_same_index
    (L t u : ℝ) (m : Fin N) :
    heatWeight (N := N) L (t - u) m * heatWeight (N := N) L u m
      = heatWeight (N := N) L t m := by
  unfold heatWeight
  rw [← Real.exp_add]
  congr 1
  ring

/--
The order-1 channel collapses to the finite heat-kernel bump trace.

This is the next bridge toward the B-side Gaussian spike kernel.
-/
theorem duhamel1Channel_eq_heat_bump_sum
    (δ : ℝ) (q : ℕ) (L : ℝ) (t u : ℝ) :
    duhamel1Channel (N := N) δ q L t u =
      ∑ m : Fin N,
        heatWeight (N := N) L t m
          * bumpMatrixElement δ q L (m + 1) (m + 1) := by
  unfold duhamel1Channel
  apply Finset.sum_congr rfl
  intro m hm
  have hheat := heatWeight_mul_same_index (N := N) L t u m
  calc
    heatWeight (N := N) L (t - u) m
        * bumpMatrixElement δ q L (m + 1) (m + 1)
        * heatWeight (N := N) L u m
        =
      (heatWeight (N := N) L (t - u) m
        * heatWeight (N := N) L u m)
        * bumpMatrixElement δ q L (m + 1) (m + 1) := by
        ring
    _ =
      heatWeight (N := N) L t m
        * bumpMatrixElement δ q L (m + 1) (m + 1) := by
        rw [hheat]

#print axioms heatWeight_mul_same_index
#print axioms duhamel1Channel_eq_heat_bump_sum

end
end RHFormalization
