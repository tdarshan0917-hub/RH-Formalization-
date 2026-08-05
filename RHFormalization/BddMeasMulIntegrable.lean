import RHFormalization.WindowedIntegrableProbe

/-!
# RHFormalization.BddMeasMulIntegrable
**The product-integrability primitive for item 3a.** A continuous function
times a bounded measurable function is interval-integrable — the single
lemma every product in the T-column Bessel expansion needs. Technique:
the probe's `mono_fun'` pattern with the continuous factor's sup on the
compact interval as the dominant.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- Continuous × (bounded measurable) is interval-integrable on `[u,v]`. -/
theorem continuous_mul_bddMeas_intervalIntegrable
    (h f : ℝ → ℝ) (hh : Continuous h) (hf : Measurable f)
    (C : ℝ) (hfC : ∀ x, |f x| ≤ C) (u v : ℝ) :
    IntervalIntegrable (fun x => h x * f x) MeasureTheory.volume u v := by
  -- sup of |h| on the compact uIcc
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x ∈ Set.uIcc u v, |h x| ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_uIcc (a := u) (b := v)).exists_bound_of_continuousOn
      (hh.abs.continuousOn)
    exact ⟨B, fun x hx => by
      have := hB x hx
      rwa [Real.norm_eq_abs, abs_abs] at this⟩
  apply IntervalIntegrable.mono_fun' (g := fun _ : ℝ => B * C)
  · exact intervalIntegrable_const
  · exact (hh.measurable.mul hf).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
    have hxIcc : x ∈ Set.uIcc u v := Set.uIoc_subset_uIcc hx
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hB x hxIcc
    have h2 := hfC x
    have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hfC 0)
    have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB u Set.left_mem_uIcc)
    exact mul_le_mul h1 h2 (abs_nonneg _) hBnn

#print axioms continuous_mul_bddMeas_intervalIntegrable

end

end RHFormalization
