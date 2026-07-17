import RHFormalization.DisplacementGaussianPenalty
import Mathlib

/-!
# D.DISP super-smoothing of the displacement majorant (manuscript p175)

The displacement sector majorant from D.DISP-2 has the form `exp x - 1 - x` with
`x = C·t^η·P(t)`, where the prime-power majorant satisfies `P(t) ≤ A·exp(-c₁/t)`
near `t = 0` (because `log q ≥ log 2` for every prime power, p175). Since `x → 0`
as `t → 0⁺`, the Mathlib bound `|exp x - 1 - x| ≤ x²` applies, and
`x² ≤ B²·exp(-2c₁/t)`. The banked `gaussian_penalty_le_pow` then turns the
`exp(-2c₁/t)` factor into `O(t^N)` for every `N`.

Displacement-sector half of D.CAN-REM local boundedness.
-/

namespace RHFormalization
open Real

/-- **Displacement majorant super-smoothing (D.DISP).** -/
theorem disp_majorant_superpoly
    (c₁ B : ℝ) (hc₁ : 0 < c₁) (hB : 0 ≤ B) (N : ℕ)
    (x : ℝ → ℝ)
    (hx0 : ∀ t, 0 < t → 0 ≤ x t)
    (hx1 : ∀ t, 0 < t → x t ≤ 1)
    (hxbd : ∀ t, 0 < t → x t ≤ B * Real.exp (-(c₁ / t))) :
    ∀ t, 0 < t →
      Real.exp (x t) - 1 - x t
        ≤ (B ^ 2) *
            (((Nat.factorial N : ℝ) / (Real.sqrt (2 * c₁)) ^ (2 * N)) * t ^ N) := by
  intro t ht
  have hxle1 : |x t| ≤ 1 := by
    rw [abs_of_nonneg (hx0 t ht)]; exact hx1 t ht
  have hstep1 : Real.exp (x t) - 1 - x t ≤ (x t) ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le hxle1
    calc Real.exp (x t) - 1 - x t ≤ |Real.exp (x t) - 1 - x t| := le_abs_self _
      _ ≤ (x t) ^ 2 := h
  have hxsq : (x t) ^ 2 ≤ B ^ 2 * Real.exp (-(2 * c₁ / t)) := by
    have hbd := hxbd t ht
    have hsq : (x t) ^ 2 ≤ (B * Real.exp (-(c₁ / t))) ^ 2 := by
      apply sq_le_sq'
      · linarith [mul_nonneg hB (Real.exp_pos (-(c₁ / t))).le, hx0 t ht]
      · exact hbd
    calc (x t) ^ 2 ≤ (B * Real.exp (-(c₁ / t))) ^ 2 := hsq
      _ = B ^ 2 * (Real.exp (-(c₁ / t))) ^ 2 := by ring
      _ = B ^ 2 * Real.exp (-(2 * c₁ / t)) := by
          have hexp2 : (Real.exp (-(c₁ / t))) ^ 2 = Real.exp (-(2 * c₁ / t)) := by
            rw [sq, ← Real.exp_add]
            congr 1
            ring
          rw [hexp2]
  have hδ : (0:ℝ) < Real.sqrt (2 * c₁) := Real.sqrt_pos.mpr (by linarith)
  have hgauss :
      Real.exp (-(2 * c₁ / t))
        ≤ ((Nat.factorial N : ℝ) / (Real.sqrt (2 * c₁)) ^ (2 * N)) * t ^ N := by
    have hmain := gaussian_penalty_le_pow (Real.sqrt (2 * c₁)) 1 hδ one_pos N t ht
    have hsqr : (Real.sqrt (2 * c₁)) ^ 2 = 2 * c₁ := Real.sq_sqrt (by linarith)
    rw [hsqr] at hmain
    simpa using hmain
  calc Real.exp (x t) - 1 - x t
      ≤ (x t) ^ 2 := hstep1
    _ ≤ B ^ 2 * Real.exp (-(2 * c₁ / t)) := hxsq
    _ ≤ B ^ 2 * (((Nat.factorial N : ℝ) / (Real.sqrt (2 * c₁)) ^ (2 * N)) * t ^ N) :=
        mul_le_mul_of_nonneg_left hgauss (sq_nonneg B)

#print axioms disp_majorant_superpoly

end RHFormalization
