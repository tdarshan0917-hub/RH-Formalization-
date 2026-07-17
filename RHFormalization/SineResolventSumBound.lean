-- SENTINEL: L1d-sine-resolvent-sum-v2
import RHFormalization.CosResolventTailBound
import RHFormalization.GalerkinSpikeSinHarmonic
import Mathlib

/-!
# L1d — The sine-correction resolvent sum
`sineResolventSum_norm_le`: on Ω with floor c,
  ‖Σ_{m : Fin N} sin(ξ_m a)·((m+1)π)⁻¹·(s+1/4+μ m)⁻¹‖
    ≤ (1/(c·π))·(1 + log N),
for any nonneg spectrum μ. Transform-domain twin of the banked
abs_spikeSinSum_le_log; resolvent factor ≤ 1/c via the floor at ξ = √(μ m).
Harmonic transfer via the BANKED sum_inv_succ_le_one_add_log. Feeds L1e.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The floor transfers to real shifts: `c ≤ ‖s + 1/4 + μ‖` for `μ ≥ 0`. -/
theorem floor_at_shift (s : ℂ) (c : ℝ) (hc : 0 < c) (μm : ℝ) (hμm : 0 ≤ μm)
    (hfl : ∀ ξ : ℝ, c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    c ≤ ‖s + (1/4 : ℂ) + ((μm : ℝ) : ℂ)‖ := by
  have h := hfl (Real.sqrt μm)
  have hsq : ((Real.sqrt μm : ℝ) : ℂ)^2 = ((μm : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hμm]
  rw [hsq] at h
  have h1 : c * 1 ≤ c * (1 + (Real.sqrt μm)^2) := by
    apply mul_le_mul_of_nonneg_left ?_ hc.le
    nlinarith [sq_nonneg (Real.sqrt μm)]
  rw [mul_one] at h1
  linarith

/-- **L1d — the sine-correction sum bound** (generic nonneg spectrum). -/
theorem sineResolventSum_norm_le (N : ℕ) (a L : ℝ) (s : ℂ)
    (μ : Fin N → ℝ) (hμ : ∀ m, 0 ≤ μ m) (c : ℝ) (hc : 0 < c)
    (hfl : ∀ ξ : ℝ, c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    ‖∑ m : Fin N,
        ((Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
            / ((((m : ℝ)) + 1) * Real.pi) : ℝ) : ℂ)
          * (1 / (s + (1/4 : ℂ) + ((μ m : ℝ) : ℂ)))‖
      ≤ (1 / (c * Real.pi)) * (1 + Real.log N) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hmode : ∀ m : Fin N,
      ‖((Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
            / ((((m : ℝ)) + 1) * Real.pi) : ℝ) : ℂ)
          * (1 / (s + (1/4 : ℂ) + ((μ m : ℝ) : ℂ)))‖
        ≤ ((((m : ℝ)) + 1) * Real.pi)⁻¹ * c⁻¹ := by
    intro m
    have hm1 : (0:ℝ) < ((m : ℝ)) + 1 := by positivity
    have hflμ := floor_at_shift s c hc (μ m) (hμ m) hfl
    have hnormpos : (0:ℝ) < ‖s + (1/4 : ℂ) + ((μ m : ℝ) : ℂ)‖ :=
      lt_of_lt_of_le hc hflμ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_one]
    have hA : |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
        / ((((m : ℝ)) + 1) * Real.pi)| ≤ ((((m : ℝ)) + 1) * Real.pi)⁻¹ := by
      rw [abs_div, div_eq_mul_inv]
      have hsin : |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      have habs : |(((m : ℝ)) + 1) * Real.pi| = (((m : ℝ)) + 1) * Real.pi :=
        abs_of_pos (by positivity)
      rw [habs]
      calc |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)|
            * ((((m : ℝ)) + 1) * Real.pi)⁻¹
          ≤ 1 * ((((m : ℝ)) + 1) * Real.pi)⁻¹ :=
            mul_le_mul_of_nonneg_right hsin (by positivity)
        _ = ((((m : ℝ)) + 1) * Real.pi)⁻¹ := one_mul _
    have hB : ‖s + (1/4 : ℂ) + ((μ m : ℝ) : ℂ)‖⁻¹ ≤ c⁻¹ :=
      inv_anti₀ hc hflμ
    calc |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi)|
          * (1 / ‖s + (1/4 : ℂ) + ((μ m : ℝ) : ℂ)‖)
        = |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi)|
          * ‖s + (1/4 : ℂ) + ((μ m : ℝ) : ℂ)‖⁻¹ := by rw [one_div]
      _ ≤ ((((m : ℝ)) + 1) * Real.pi)⁻¹ * c⁻¹ :=
          mul_le_mul hA hB (by positivity) (by positivity)
  have hsum : ‖∑ m : Fin N,
      ((Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi) : ℝ) : ℂ)
        * (1 / (s + (1/4 : ℂ) + ((μ m : ℝ) : ℂ)))‖
      ≤ ∑ m : Fin N, ((((m : ℝ)) + 1) * Real.pi)⁻¹ * c⁻¹ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => hmode m))
  have hconv : (∑ m : Fin N, ((((m : ℝ)) + 1) * Real.pi)⁻¹ * c⁻¹)
      = (1 / (c * Real.pi)) * ∑ i ∈ Finset.range N, (((i : ℝ)) + 1)⁻¹ := by
    rw [Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range
        (fun i => (1 / (c * Real.pi)) * (((i : ℝ)) + 1)⁻¹) N]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_inv, one_div, mul_inv]
    ring
  have hcπ : (0:ℝ) ≤ 1 / (c * Real.pi) := by positivity
  calc ‖∑ m : Fin N,
      ((Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi) : ℝ) : ℂ)
        * (1 / (s + (1/4 : ℂ) + ((μ m : ℝ) : ℂ)))‖
      ≤ ∑ m : Fin N, ((((m : ℝ)) + 1) * Real.pi)⁻¹ * c⁻¹ := hsum
    _ = (1 / (c * Real.pi)) * ∑ i ∈ Finset.range N, (((i : ℝ)) + 1)⁻¹ := hconv
    _ ≤ (1 / (c * Real.pi)) * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left (sum_inv_succ_le_one_add_log N) hcπ

#print axioms floor_at_shift
#print axioms sineResolventSum_norm_le

end

end RHFormalization
