import RHFormalization.DispMajorantSuperpoly
import Mathlib

/-!
# D.DISP-3 integrability of the displacement integrand (manuscript p175)

The displacement transform integrand `t^(-β)·(exp(x t) - 1 - x t)` is integrable on
`(0, t₀]`. By `disp_majorant_superpoly` the bracket is `≤ C_N·t^N` for every `N`;
choosing `N` with `N - β > -1` dominates the integrand by the integrable power
`C·t^(N-β)` (Mathlib `intervalIntegrable_rpow'`). Core of (D.DISP-3).

Backwards from RH: displacement sector locally bounded ⟸ this integrability.
-/

namespace RHFormalization
open Real MeasureTheory

/-- **D.DISP-3 integrability core.** -/
theorem disp_integrand_integrable
    (c₁ B β t₀ : ℝ) (hc₁ : 0 < c₁) (hB : 0 ≤ B) (hβ : 0 ≤ β) (ht₀ : 0 < t₀)
    (N : ℕ) (hNβ : β < N)
    (x : ℝ → ℝ) (hxcont : Continuous x)
    (hx0 : ∀ t, 0 < t → 0 ≤ x t)
    (hx1 : ∀ t, 0 < t → x t ≤ 1)
    (hxbd : ∀ t, 0 < t → x t ≤ B * Real.exp (-(c₁ / t))) :
    IntervalIntegrable
      (fun t => t ^ (-β) * (Real.exp (x t) - 1 - x t)) volume 0 t₀ := by
  set C : ℝ := (B ^ 2) * ((Nat.factorial N : ℝ) / (Real.sqrt (2 * c₁)) ^ (2 * N)) with hC
  have hCnn : 0 ≤ C := by
    apply mul_nonneg (sq_nonneg B)
    apply div_nonneg (by positivity); positivity
  have hrpow : IntervalIntegrable (fun t : ℝ => t ^ ((N : ℝ) - β)) volume 0 t₀ := by
    have hβN : β ≤ (N:ℝ) := le_of_lt (by exact_mod_cast hNβ)
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hdom : IntervalIntegrable (fun t : ℝ => C * t ^ ((N : ℝ) - β)) volume 0 t₀ :=
    hrpow.const_mul C
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht₀.le] at hdom ⊢
  apply Integrable.mono' hdom
  · -- a.e.-strongly-measurable on Ioc 0 t₀: integrand is ContinuousOn (0,t₀]
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.mul
    · -- t^(-β) continuous on Ioc 0 t₀ (t > 0 there)
      apply ContinuousOn.rpow_const continuousOn_id
      intro t ht
      exact Or.inl (ne_of_gt ht.1)
    · -- exp(x t) - 1 - x t continuous everywhere
      exact (((Real.continuous_exp.comp hxcont).sub continuous_const).sub hxcont).continuousOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    obtain ⟨htpos, htle⟩ := ht
    have hmaj := disp_majorant_superpoly c₁ B hc₁ hB N x hx0 hx1 hxbd t htpos
    have hbr_nn : 0 ≤ Real.exp (x t) - 1 - x t := by
      have := Real.add_one_le_exp (x t); linarith
    have htβ_nn : 0 ≤ t ^ (-β) := Real.rpow_nonneg htpos.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htβ_nn hbr_nn)]
    calc t ^ (-β) * (Real.exp (x t) - 1 - x t)
        ≤ t ^ (-β) * (C * t ^ (N:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ htβ_nn
          have : Real.exp (x t) - 1 - x t ≤ C * t ^ N := by
            simpa [hC, mul_assoc] using hmaj
          rwa [← Real.rpow_natCast t N] at this
      _ = C * t ^ ((N:ℝ) - β) := by
          rw [show t ^ (-β) * (C * t ^ (N:ℝ)) = C * (t ^ (-β) * t ^ (N:ℝ)) by ring,
             ← Real.rpow_add htpos]
          ring_nf

#print axioms disp_integrand_integrable

end RHFormalization
