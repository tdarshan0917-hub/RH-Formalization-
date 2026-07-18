-- SENTINEL: spike-transfer-rate-m1-integral-v1
import RHFormalization.SpikeTransferRateM1
import Mathlib

/-! # Core brick 2 — D.BFF.5 at M=1, integrated: `|E₁(t)| ≤ B²N²·t`.
The first complete D.SPIKE-TRANSFER inequality of the formalization:
the order-2 Duhamel remainder integral is linear in `t` at fixed cutoff.
No integrability obligations (`norm_integral_le_of_norm_le_const`).
Hypothesis-free. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- **CORE BRICK 2 (D.BFF.5, M=1, integrated).** -/
theorem duhamel2Integral_abs_le_linear
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L : ℝ) (hL : 0 < L) (t : ℝ) (ht : 0 ≤ t) :
    |∫ u in (0:ℝ)..t, duhamel2Integrand (N := N) δ qs w L t u|
      ≤ ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
          * ((N : ℝ) * (N : ℝ)) * t := by
  set C : ℝ := ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
      * ((N : ℝ) * (N : ℝ)) with hC
  have hbound : ∀ u ∈ Set.uIoc (0:ℝ) t,
      ‖duhamel2Integrand (N := N) δ qs w L t u‖ ≤ C := by
    intro u hu
    have huIoc : u ∈ Set.Ioc (0:ℝ) t := by
      first
        | (rwa [Set.uIoc_of_le ht] at hu)
        | (rw [Set.uIoc_of_le ht] at hu; exact hu)
    rw [Real.norm_eq_abs]
    exact duhamel2Integrand_abs_le_card_sq δ hδ qs w L hL t u
      huIoc.1.le huIoc.2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at h
  have habs : |t - 0| = t := by
    rw [sub_zero]
    exact abs_of_nonneg ht
  rw [habs] at h
  exact h

#print axioms duhamel2Integral_abs_le_linear

end

end RHFormalization
