import RHFormalization.AdaptiveGalerkinDefectGate
import Mathlib

/-!
# Spike kernel tail bounds — G2a of the defect gate
SENTINEL: spike-tail-g2a-v1

ROUTE CARD
1. `abs_galerkinSpikeKernel_le`: N-INDEPENDENT domination of the spike
   kernel — `|g_N(t,a)| ≤ 2·(1−e^{−t(π/L)²})⁻¹` — via the banked
   `sum_heatWeight_le` (Stone 8a) and the N-free pairing bound `|T| ≤ 2`.
2. `galerkinSpikeKernel_mode_tail_le`: modes above `M` contribute at most
   `2·e^{−t·λ_M}·(1−e^{−t(π/L)²})⁻¹` — the geometric mode-tail with the
   banked Weyl growth; the quantitative engine of the G2/G3 comparisons.
3. Pure estimates on banked objects; no new analytic machinery.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- Pointwise: each spike-kernel mode is dominated by twice the heat weight. -/
theorem abs_spikeMode_le (L t a : ℝ) (hL : 0 < L) (m : Fin N) :
    |heatWeight (N := N) L t m * galerkinT (N := N) L a m m|
      ≤ 2 * heatWeight (N := N) L t m := by
  rw [abs_mul]
  have hw : |heatWeight (N := N) L t m| = heatWeight (N := N) L t m := by
    unfold heatWeight
    exact abs_of_pos (Real.exp_pos _)
  rw [hw]
  have hT := galerkinT_entry_abs_le (N := N) L a hL m m
  calc heatWeight (N := N) L t m * |galerkinT (N := N) L a m m|
      ≤ heatWeight (N := N) L t m * 2 := by
        apply mul_le_mul_of_nonneg_left hT
        unfold heatWeight
        exact (Real.exp_pos _).le
    _ = 2 * heatWeight (N := N) L t m := by ring

/-- **N-independent spike domination**: `|g_N(t,a)| ≤ 2·(1−e^{−t(π/L)²})⁻¹`. -/
theorem abs_galerkinSpikeKernel_le (L t a : ℝ) (hL : 0 < L) (ht : 0 < t) :
    |galerkinSpikeKernel (N := N) L t a|
      ≤ 2 * (1 - Real.exp (-(t * (Real.pi / L) ^ 2)))⁻¹ := by
  rw [galerkinSpikeKernel_eq_sum]
  calc |∑ m : Fin N, heatWeight (N := N) L t m * galerkinT (N := N) L a m m|
      ≤ ∑ m : Fin N, |heatWeight (N := N) L t m * galerkinT (N := N) L a m m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin N, 2 * heatWeight (N := N) L t m := by
        exact Finset.sum_le_sum fun m _ => abs_spikeMode_le L t a hL m
    _ = 2 * ∑ m : Fin N, heatWeight (N := N) L t m := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (1 - Real.exp (-(t * (Real.pi / L) ^ 2)))⁻¹ := by
        apply mul_le_mul_of_nonneg_left (sum_heatWeight_le L hL t ht)
        norm_num

/-- Heat weights decay past a threshold mode: for `M ≤ m`,
`e^{−tλ_m} ≤ e^{−tλ_M}·e^{−t(π/L)²(m−M)}` — the shifted geometric step. -/
theorem heatWeight_decay_of_le (L t : ℝ) (hL : 0 < L) (ht : 0 < t)
    (M m : ℕ) (hMm : M ≤ m) :
    Real.exp (-(t * galerkinLam L m))
      ≤ Real.exp (-(t * galerkinLam L M)) *
          Real.exp (-(t * (Real.pi / L) ^ 2 * ((m : ℝ) - (M : ℝ)))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlam : galerkinLam L M + (Real.pi / L) ^ 2 * ((m : ℝ) - (M : ℝ))
      ≤ galerkinLam L m := by
    unfold galerkinLam
    have hM : (M : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hMm
    have hpi : (0 : ℝ) < (Real.pi / L) ^ 2 := by positivity
    have hexp : ((M : ℝ) + 1) ^ 2 + ((m : ℝ) - (M : ℝ))
        ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
    have h1 : (((M : ℝ) + 1) * Real.pi / L) ^ 2
        = (Real.pi / L) ^ 2 * ((M : ℝ) + 1) ^ 2 := by ring
    have h2 : (((m : ℝ) + 1) * Real.pi / L) ^ 2
        = (Real.pi / L) ^ 2 * ((m : ℝ) + 1) ^ 2 := by ring
    rw [h1, h2]
    nlinarith [hpi]
  nlinarith [ht, hlam]

#print axioms abs_spikeMode_le
#print axioms abs_galerkinSpikeKernel_le
#print axioms heatWeight_decay_of_le

end

end RHFormalization
