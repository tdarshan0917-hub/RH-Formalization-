import Mathlib

/-!
# AnchorFiniteGeneral — D.ADM anchor finiteness at ARBITRARY coupling

`AnchorFinite.anchor_integrand_integrable` requires `c * B ≤ 1`, which fails on
large stages (sup V# ~ e^{R/2}, coupling C*·t0 fixed). This file removes that
restriction: for any c ≥ 0 and any nonnegative, bounded, integrable V,
`exp(cV) - 1 - cV` is integrable, dominated by `(c·e^{cB})·V`.

Also: the D.ADM-NET window choice in schedule-preserving form —
`L := max L0 M` gives `M/(2L) ≤ 1` while keeping `L0 ≤ L`, so every banked
lower bound on the window survives the adaptive re-tuning.
-/

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory

/-- Pointwise key: for `x ≥ 0`, `0 ≤ e^x - 1 - x ≤ x·e^x`. Upper half. -/
theorem exp_sub_one_sub_le_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ x * Real.exp x := by
  have hEpos : 0 < Real.exp x := Real.exp_pos x
  have h1 : (-x) + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have h3 : (1 - x) * Real.exp x ≤ 1 := by
    have h1' : 1 - x ≤ (Real.exp x)⁻¹ := by rw [← h2]; linarith
    calc (1 - x) * Real.exp x
        ≤ (Real.exp x)⁻¹ * Real.exp x :=
          mul_le_mul_of_nonneg_right h1' hEpos.le
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hEpos)
    
  nlinarith [hx, hEpos]

/-- **D.ADM anchor finiteness, general coupling.** No `c*B ≤ 1` needed. -/
theorem anchor_integrand_integrable_general
    (V : ℝ → ℝ) (c B : ℝ) (hc : 0 ≤ c)
    (hVnn : ∀ u, 0 ≤ V u)
    (hVbd : ∀ u, V u ≤ B)
    (hVmeas : Measurable V)
    (hV_int : Integrable V volume) :
    Integrable (fun u => Real.exp (c * V u) - 1 - c * V u) volume := by
  have hdom : Integrable (fun u => (c * Real.exp (c * B)) * V u) volume :=
    hV_int.const_mul _
  apply Integrable.mono' hdom
  · apply Measurable.aestronglyMeasurable
    exact ((Real.measurable_exp.comp (measurable_const.mul hVmeas)).sub
      measurable_const).sub (measurable_const.mul hVmeas)
  · filter_upwards with u
    have hxnn : 0 ≤ c * V u := mul_nonneg hc (hVnn u)
    have hlow : 0 ≤ Real.exp (c * V u) - 1 - c * V u := by
      have := Real.add_one_le_exp (c * V u)
      linarith
    have hup : Real.exp (c * V u) - 1 - c * V u
        ≤ (c * Real.exp (c * B)) * V u := by
      have hkey := exp_sub_one_sub_le_mul_exp hxnn
      have hxe : Real.exp (c * V u) ≤ Real.exp (c * B) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hVbd u) hc)
      have h5 : (c * V u) * Real.exp (c * V u)
          ≤ (c * V u) * Real.exp (c * B) :=
        mul_le_mul_of_nonneg_left hxe hxnn
      calc Real.exp (c * V u) - 1 - c * V u
          ≤ (c * V u) * Real.exp (c * V u) := hkey
        _ ≤ (c * V u) * Real.exp (c * B) := h5
        _ = (c * Real.exp (c * B)) * V u := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg hlow]
    exact hup

/-- The anchor value is nonnegative (for the sup/le bookkeeping in D.ADM). -/
theorem anchor_value_nonneg
    (V : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hVnn : ∀ u, 0 ≤ V u) :
    0 ≤ ∫ u, (Real.exp (c * V u) - 1 - c * V u) := by
  apply integral_nonneg
  intro u
  have := Real.add_one_le_exp (c * V u)
  simp only [Pi.zero_apply]
  linarith

/-- **D.ADM-NET window choice, schedule-preserving.** Choosing
`L := max L0 M` gives `M/(2L) ≤ 1` while retaining `L0 ≤ L`, so all banked
lower-bound facts about the window survive. -/
theorem adaptive_window_bound
    (M L0 : ℝ) (hM : 0 ≤ M) (hL0 : 1 ≤ L0) :
    M / (2 * max L0 M) ≤ 1 := by
  have hmaxpos : 0 < max L0 M :=
    lt_of_lt_of_le zero_lt_one (le_trans hL0 (le_max_left L0 M))
  have hMle : M ≤ max L0 M := le_max_right L0 M
  rw [div_le_one (by positivity)]
  nlinarith [hmaxpos, hMle]

theorem adaptive_window_ge (M L0 : ℝ) : L0 ≤ max L0 M := le_max_left L0 M

#print axioms exp_sub_one_sub_le_mul_exp
#print axioms anchor_integrand_integrable_general
#print axioms anchor_value_nonneg
#print axioms adaptive_window_bound

end RHFormalization
