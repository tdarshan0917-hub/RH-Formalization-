import RHFormalization.BSideHeatKernelLaplace
import RHFormalization.BSideHeatKernelLaplaceEnvelope
import Mathlib

namespace RHFormalization
open Complex MeasureTheory Set Filter Metric

/-- RHS of the B-side connector, as a function of `s`. -/
noncomputable def bRHS (a : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0:ℝ), shiftedHeatIntegrand a s t

/-- The Laplace-transform side is complex-differentiable on the right half-plane. -/
lemma bRHS_differentiableAt (a : ℝ) (s₀ : ℂ) (hs₀ : 0 < s₀.re) :
    DifferentiableAt ℂ (bRHS a) s₀ := by
  have hδ0 : 0 < s₀.re / 2 := by linarith
  set δ : ℝ := s₀.re / 2 with hδdef
  set U : Set ℂ := {s : ℂ | δ < s.re} with hUdef
  have hUnhds : U ∈ nhds s₀ := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
    simp only [Set.mem_setOf_eq, hδdef]
    linarith

  have hmeas_one : ∀ (z : ℂ),
      AEStronglyMeasurable (fun t : ℝ => shiftedHeatIntegrand a z t) (volume.restrict (Ioi 0)) := by
    intro z
    unfold shiftedHeatIntegrand heatKernelG
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmeas : ∀ᶠ (z : ℂ) in nhds s₀,
      AEStronglyMeasurable (fun t : ℝ => shiftedHeatIntegrand a z t) (volume.restrict (Ioi 0)) :=
    Filter.Eventually.of_forall hmeas_one

  have hce : 0 < s₀.re + 1/4 := by linarith
  have hint0 : IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a s₀ t) (Ioi 0) volume := by
    refine (bEnvelope_integrable (s₀.re + 1/4) hce).mono' (hmeas_one s₀) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact shiftedHeatIntegrand_norm_le_bEnvelope a s₀ t ht

  have hderiv_meas : AEStronglyMeasurable
      (fun t : ℝ => -(t:ℂ) * shiftedHeatIntegrand a s₀ t) (volume.restrict (Ioi 0)) := by
    apply AEStronglyMeasurable.mul ?_ (hmeas_one s₀)
    apply Measurable.aestronglyMeasurable
    fun_prop

  have hbound : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi 0)), ∀ z ∈ U,
      ‖-(t:ℂ) * shiftedHeatIntegrand a z t‖ ≤ dEnvelope δ t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    intro z hz
    have ht0 : 0 < t := ht
    have hzre : δ < z.re := hz
    have hnorm := shiftedHeatIntegrand_norm_le_bEnvelope a z t ht0
    have hstep : ‖-(t:ℂ) * shiftedHeatIntegrand a z t‖ = t * ‖shiftedHeatIntegrand a z t‖ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    rw [hstep]
    have hmono : bEnvelope (z.re + 1/4) t ≤ bEnvelope δ t := by
      unfold bEnvelope
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [ht0]
    unfold dEnvelope
    calc t * ‖shiftedHeatIntegrand a z t‖
        ≤ t * bEnvelope (z.re + 1/4) t := mul_le_mul_of_nonneg_left hnorm ht0.le
      _ ≤ t * bEnvelope δ t := mul_le_mul_of_nonneg_left hmono ht0.le

  have hbound_int : IntegrableOn (dEnvelope δ) (Ioi 0) volume := dEnvelope_integrable δ hδ0

  have hderiv : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi 0)), ∀ z ∈ U,
      HasDerivAt (fun w : ℂ => shiftedHeatIntegrand a w t)
        (-(t:ℂ) * shiftedHeatIntegrand a z t) z := by
    filter_upwards with t
    intro z _
    exact shiftedHeatIntegrand_hasDerivAt a t z

  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := dEnvelope δ) (F := fun z t => shiftedHeatIntegrand a z t)
    (F' := fun z t => -(t:ℂ) * shiftedHeatIntegrand a z t)
    hUnhds hmeas hint0 hderiv_meas hbound hbound_int hderiv
  exact result.2.differentiableAt

#print axioms bRHS_differentiableAt

end RHFormalization
