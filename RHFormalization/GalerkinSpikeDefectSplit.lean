import RHFormalization.GalerkinDiagonalFormula
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.IntegralCosGaussianReal
import Mathlib

/-!
# Spike defect split — G3-ii-a of the defect gate
SENTINEL: defect-split-v5

ROUTE CARD
1. Exact split (BANKED in v2, reproved here): `g_N = (1−a/L)·spikeCosSum
   + spikeSinSum` for 0 ≤ a ≤ L.
2. E_sin CLOSED: `|spikeSinSum| ≤ (1/π)·(1−e^{−t(π/L)²})⁻¹`.
3. v3: dead hfrac block removed; fraction bound via mul_le_mul (no
   div_le_div name roulette); heatWeight matched by unfolding to exp form.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- The pure cosine mode sum: main term of the diagonal formula. -/
def spikeCosSum (N : ℕ) (L t a : ℝ) : ℝ :=
  ∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) *
    Real.cos (((m : ℝ) + 1) * Real.pi * a / L)

/-- The sin-correction sum: second term of the diagonal formula. -/
def spikeSinSum (N : ℕ) (L t a : ℝ) : ℝ :=
  ∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) *
    (Real.sin (((m : ℝ) + 1) * Real.pi * a / L) / ((((m : ℝ)) + 1) * Real.pi))

/-- **The exact spike-kernel split** (banked diagonal formula, summed). -/
theorem galerkinSpikeKernel_split (L t a : ℝ) (hL : 0 < L)
    (ha0 : 0 ≤ a) (haL : a ≤ L) :
    galerkinSpikeKernel (N := N) L t a
      = (1 - a / L) * spikeCosSum N L t a + spikeSinSum N L t a := by
  rw [galerkinSpikeKernel_eq_sum]
  unfold spikeCosSum spikeSinSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [galerkinT_diag_formula L a hL ha0 haL m]
  have hw : heatWeight (N := N) L t m
      = Real.exp (-(t * galerkinLam L (m : ℕ))) := rfl
  rw [hw]
  ring

/-- Per-mode sin bound: `|exp·sin/((m+1)π)| ≤ (1/π)·exp`. -/
theorem abs_sinMode_le (L t a : ℝ) (m : Fin N) :
    |Real.exp (-(t * galerkinLam L (m : ℕ))) *
        (Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi))|
      ≤ (1 / Real.pi) * Real.exp (-(t * galerkinLam L (m : ℕ))) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_div]
  have hm1pos : (0 : ℝ) < ((m : ℝ) + 1) * Real.pi := by positivity
  rw [abs_of_pos hm1pos]
  have hsin : |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  -- multiplication-side: sin/((m+1)π) ≤ 1/π  ⟺  sin·π ≤ (m+1)π  (all pos)
  have hkey : |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)|
      / (((m : ℝ) + 1) * Real.pi) ≤ 1 / Real.pi := by
    have hd : Real.pi ≤ ((m : ℝ) + 1) * Real.pi := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      nlinarith [Real.pi_pos]
    have hinv : (((m : ℝ) + 1) * Real.pi)⁻¹ ≤ Real.pi⁻¹ := by
      first
        | exact inv_anti₀ Real.pi_pos hd
        | exact inv_le_inv_of_le Real.pi_pos hd
        | (apply inv_le_inv_of_le Real.pi_pos hd)
    calc |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)|
          / (((m : ℝ) + 1) * Real.pi)
        = |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)|
            * (((m : ℝ) + 1) * Real.pi)⁻¹ := by
          rw [div_eq_mul_inv]
      _ ≤ 1 * Real.pi⁻¹ := by
          apply mul_le_mul hsin hinv (by positivity) (by norm_num)
      _ = 1 / Real.pi := by rw [one_mul, one_div]
  calc Real.exp (-(t * galerkinLam L (m : ℕ))) *
        (|Real.sin (((m : ℝ) + 1) * Real.pi * a / L)|
          / (((m : ℝ) + 1) * Real.pi))
      ≤ Real.exp (-(t * galerkinLam L (m : ℕ))) * (1 / Real.pi) :=
        mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
    _ = (1 / Real.pi) * Real.exp (-(t * galerkinLam L (m : ℕ))) := by ring

/-- **E_sin CLOSED**: N-free bound on the sin-correction. -/
theorem abs_spikeSinSum_le (L t a : ℝ) (hL : 0 < L) (ht : 0 < t) :
    |spikeSinSum N L t a|
      ≤ (1 / Real.pi) * (1 - Real.exp (-(t * (Real.pi / L) ^ 2)))⁻¹ := by
  unfold spikeSinSum
  have hstep1 : |∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) *
        (Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi))|
      ≤ ∑ m : Fin N, (1 / Real.pi) * Real.exp (-(t * galerkinLam L (m : ℕ))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun m _ => abs_sinMode_le L t a m
  have hstep2 : ∑ m : Fin N, (1 / Real.pi) *
        Real.exp (-(t * galerkinLam L (m : ℕ)))
      = (1 / Real.pi) * ∑ m : Fin N, heatWeight (N := N) L t m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rfl
  have hstep3 : (1 / Real.pi) * ∑ m : Fin N, heatWeight (N := N) L t m
      ≤ (1 / Real.pi) * (1 - Real.exp (-(t * (Real.pi / L) ^ 2)))⁻¹ := by
    apply mul_le_mul_of_nonneg_left (sum_heatWeight_le L hL t ht)
    positivity
  linarith [hstep1, hstep2 ▸ hstep1, hstep3]

#print axioms spikeCosSum
#print axioms spikeSinSum
#print axioms galerkinSpikeKernel_split
#print axioms abs_sinMode_le
#print axioms abs_spikeSinSum_le

end

end RHFormalization
