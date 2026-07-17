import RHFormalization.AdmissibleGalerkinStage
import RHFormalization.BSideHeatKernelLaplaceConnector
import RHFormalization.BSideHeatKernelLaplaceEnvelope
import RHFormalization.ShiftedLaplaceMajorant
import Mathlib

/-!
# RHFormalization.GalerkinBSideLaplace

**Galerkin Stieltjes rep, B-side.** The finite prime-power B-stage at the
admissible net is the Laplace transform of its spike integrand on `re s > 0`.
No `hcenter` hypothesis: `center_nonneg` is unconditional.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory Set
open scoped BigOperators

/-- The shifted heat integrand is integrable on `(0,∞)` for `re s > 0`. -/
lemma shiftedHeatIntegrand_integrableOn (a : ℝ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a s t) (Ioi 0) volume := by
  have hce : 0 < s.re + 1/4 := by linarith
  have hmeas : AEStronglyMeasurable (fun t : ℝ => shiftedHeatIntegrand a s t)
      (volume.restrict (Ioi 0)) := by
    unfold shiftedHeatIntegrand heatKernelG
    apply Measurable.aestronglyMeasurable
    fun_prop
  refine (bEnvelope_integrable (s.re + 1/4) hce).mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact shiftedHeatIntegrand_norm_le_bEnvelope a s t ht

/-- **B-side Galerkin Stieltjes rep.** -/
theorem galerkin_B_stage_eq_laplace (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      = ∫ t in Ioi (0:ℝ),
          ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            q.weightC * shiftedHeatIntegrand q.center s t := by
  have hB : galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC * shiftedLaplaceHeatKernelC q.center s := rfl
  rw [hB]
  rw [MeasureTheory.integral_finset_sum
      (activePrimePowerPairsCenterBelow (admR n))
      (fun q _ => (shiftedHeatIntegrand_integrableOn q.center s hs).const_mul q.weightC)]
  apply Finset.sum_congr rfl
  intro q _
  rw [shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane
        q.center (center_nonneg q) s hs]
  simp [MeasureTheory.integral_const_mul]

#print axioms shiftedHeatIntegrand_integrableOn
#print axioms galerkin_B_stage_eq_laplace

end RHFormalization
