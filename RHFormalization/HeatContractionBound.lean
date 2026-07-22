-- SENTINEL: CONTRACT-v2
import RHFormalization.GalerkinDuhamelUniformBound
import RHFormalization.SpikeTransferRateM1
import RHFormalization.DBFFDecodedProfilesLoc
import Mathlib

/-!
# HeatContractionBound — B3c stone 2 of 5: the free heat semigroup is a
linftyOp CONTRACTION

`‖diagonal (heatWeight L t)‖ ≤ 1` for t ≥ 0. This is the load-bearing fact
of the word-expansion mechanism: every Duhamel word then costs at most
`∏‖heat factors‖·∏‖V‖ ≤ ‖V‖^k` with NO dimension factor — the exact point
where the (dead, Q2-frozen) E2/Frobenius route paid N^{5/2}. Consumers:
stone 3 (`‖exp(-t(K+V))‖ ≤ e^{t‖V‖}`), stone 4 (order-≥2 word tail =
e^x − 1 − x anchor form).
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- linftyOp norm of a real diagonal matrix is the sup of entry norms. -/
theorem diagonal_linfty_norm_le {d : Fin N → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, |d i| ≤ C) :
    ‖Matrix.diagonal d‖ ≤ C := by
  first
    | (rw [Matrix.linfty_opNorm_diagonal]
       first
         | (rw [pi_norm_le_iff_of_nonneg hC]
            intro i
            rw [Real.norm_eq_abs]
            exact hd i)
         | (refine (pi_norm_le_iff_of_nonneg hC).mpr fun i => ?_
            rw [Real.norm_eq_abs]
            exact hd i)
         | (rcases Nat.eq_zero_or_pos N with h0 | hpos
            · subst h0
              simp [norm_le_iff_of_nonneg]
              first
                | exact hC
                | simpa using hC
            · rw [pi_norm_le_iff_of_nonneg hC]
              intro i
              rw [Real.norm_eq_abs]
              exact hd i))
    | (refine le_trans (le_of_eq (Matrix.linfty_opNorm_diagonal d)) ?_
       first
         | (rw [pi_norm_le_iff_of_nonneg hC]
            intro i
            rw [Real.norm_eq_abs]
            exact hd i)
         | (refine (pi_norm_le_iff_of_nonneg hC).mpr fun i => ?_
            rw [Real.norm_eq_abs]
            exact hd i))


/-- **THE CONTRACTION**: the free heat diagonal has linftyOp norm ≤ 1
for every t ≥ 0. -/
theorem heat_diagonal_contraction (L t : ℝ) (ht : 0 ≤ t) :
    ‖Matrix.diagonal (heatWeight (N := N) L t)‖ ≤ 1 := by
  refine diagonal_linfty_norm_le (by norm_num) fun m => ?_
  have h1 : 0 ≤ heatWeight (N := N) L t m := by
    unfold heatWeight
    positivity
  have h2 : heatWeight (N := N) L t m ≤ 1 := heatWeight_le_one L t ht m
  rw [abs_of_nonneg h1]
  exact h2

#print axioms diagonal_linfty_norm_le
#print axioms heat_diagonal_contraction

end RHFormalization
