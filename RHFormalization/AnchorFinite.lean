import Mathlib

/-!
# D.ADM local-sector anchor finiteness (manuscript p176-177)

The locally-admissible anchor `M(R) = ∫(e^{c·V(u)} - 1 - c·V(u)) du` is finite,
where `V = V#_R` is the finite prime-power envelope `∑_{log q ≤ R} w(q)·|W(u - a_q)|`
— a finite sum of shifted Schwartz bumps, hence bounded, nonnegative, with `V²`
integrable. Since `[exp(cV) - 1 - cV] ≤ (cV)²` (Mathlib `abs_exp_sub_one_sub_id_le`)
and `V²` is integrable, `M(R) < ∞`.

Local-sector contribution to D.CAN-REM (the `M(R)/(2L) ≤ 1` engine: fix R, then
choose L large — `anchor_admissible`).

Backwards from RH: {R_α} locally bounded ⟸ local sector bounded ⟸ M(R) < ∞.
-/

namespace RHFormalization
open Real MeasureTheory

/-- **D.ADM anchor finiteness.** -/
theorem anchor_integrand_integrable
    (V : ℝ → ℝ) (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hVnn : ∀ u, 0 ≤ V u)
    (hVbd : ∀ u, V u ≤ B)
    (hcB : c * B ≤ 1)
    (hVmeas : Measurable V)
    (hVsq_int : Integrable (fun u => (V u) ^ 2) volume) :
    Integrable (fun u => Real.exp (c * V u) - 1 - c * V u) volume := by
  have hdom : Integrable (fun u => c ^ 2 * (V u) ^ 2) volume :=
    hVsq_int.const_mul (c ^ 2)
  apply Integrable.mono' hdom
  · apply Measurable.aestronglyMeasurable
    exact ((Real.measurable_exp.comp (measurable_const.mul hVmeas)).sub measurable_const).sub
      (measurable_const.mul hVmeas)
  · filter_upwards with u
    have hx : c * V u ≤ 1 := by
      calc c * V u ≤ c * B := mul_le_mul_of_nonneg_left (hVbd u) hc
        _ ≤ 1 := hcB
    have hxnn : 0 ≤ c * V u := mul_nonneg hc (hVnn u)
    have habs : |c * V u| ≤ 1 := by rw [abs_of_nonneg hxnn]; exact hx
    have hbound := Real.abs_exp_sub_one_sub_id_le habs
    have hgoal : |Real.exp (c * V u) - 1 - c * V u| ≤ c ^ 2 * (V u) ^ 2 := by
      calc |Real.exp (c * V u) - 1 - c * V u| ≤ (c * V u) ^ 2 := hbound
        _ = c ^ 2 * (V u) ^ 2 := by ring
    rw [Real.norm_eq_abs]
    exact hgoal

/-- **D.ADM admissibility: after fixing R, choose L large.** -/
theorem anchor_admissible (M : ℝ) (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 < L ∧ M / (2 * L) ≤ 1 := by
  refine ⟨M / 2 + 1, by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  nlinarith [hM]

#print axioms anchor_integrand_integrable
#print axioms anchor_admissible

end RHFormalization
