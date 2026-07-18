-- SENTINEL: dmr-btail-halfplane-bound-v6
import RHFormalization.DMRSectorTimeSplit
import RHFormalization.DMROverlapBStageBound
import RHFormalization.CanonicalPrimePowerWeightEnvelope
import RHFormalization.AdmissibleWeightNonneg
import Mathlib

/-! # Step 2a: B-package tail uniformly bounded on Re s ≥ σ > 0 (hypothesis-free). -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators Classical

theorem shiftedHeatIntegrand_at_real (a σ t : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧
      shiftedHeatIntegrand a ((σ:ℝ):ℂ) t = ((r:ℝ):ℂ) := by
  refine ⟨Real.exp (-σ * t) * Real.exp (-t/4)
    * ((1:ℝ) / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a^2) / (4*t))),
    by positivity, ?_⟩
  unfold shiftedHeatIntegrand heatKernelG
  have h1 : (-((σ:ℝ):ℂ) * (t:ℂ)) = (((-σ * t : ℝ)):ℂ) := by push_cast; ring
  have h2 : (-(t:ℂ)/4) = (((-t/4 : ℝ)):ℂ) := by push_cast; ring
  rw [h1, h2, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast
  ring

theorem shiftedHeatIntegrand_norm_mono (a : ℝ) (σ : ℝ) {s : ℂ}
    (hσs : σ ≤ s.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖shiftedHeatIntegrand a s t‖ ≤ ‖shiftedHeatIntegrand a ((σ:ℝ):ℂ) t‖ := by
  unfold shiftedHeatIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_exp]
  have h12 : (-s * (t:ℂ)).re ≤ (-((σ:ℝ):ℂ) * (t:ℂ)).re := by
    have e1 : (-s * (t:ℂ)).re = -s.re * t := by simp [Complex.mul_re]
    have e2 : (-((σ:ℝ):ℂ) * (t:ℂ)).re = -σ * t := by simp [Complex.mul_re]
    rw [e1, e2]
    nlinarith
  have hmono := Real.exp_le_exp.mpr h12
  have hrest : (0:ℝ) ≤ Real.exp ((-(t:ℂ)/4).re) * ‖heatKernelG t a‖ := by
    positivity
  calc Real.exp ((-s * (t:ℂ)).re) * Real.exp ((-(t:ℂ)/4).re)
        * ‖heatKernelG t a‖
      = Real.exp ((-s * (t:ℂ)).re)
          * (Real.exp ((-(t:ℂ)/4).re) * ‖heatKernelG t a‖) := by ring
    _ ≤ Real.exp ((-((σ:ℝ):ℂ) * (t:ℂ)).re)
          * (Real.exp ((-(t:ℂ)/4).re) * ‖heatKernelG t a‖) :=
        mul_le_mul_of_nonneg_right hmono hrest
    _ = Real.exp ((-((σ:ℝ):ℂ) * (t:ℂ)).re) * Real.exp ((-(t:ℂ)/4).re)
          * ‖heatKernelG t a‖ := by ring

theorem kernel_at_real_point (a σ : ℝ) (hσ : 0 < σ) :
    ∃ v : ℝ, 0 ≤ v ∧
      shiftedLaplaceHeatKernelC a ((σ:ℝ):ℂ) = ((v:ℝ):ℂ) := by
  have hnn : (0:ℝ) ≤ σ + 1/4 := by linarith
  have hcast : ((σ:ℝ):ℂ) + (1/4:ℂ) = (((σ + 1/4 : ℝ)):ℂ) := by push_cast; ring
  have hsq : Complex.sqrt (((σ:ℝ):ℂ) + (1/4:ℂ))
      = ((Real.sqrt (σ + 1/4) : ℝ):ℂ) := by
    rw [hcast]
    unfold Complex.sqrt
    have h2c : ((2:ℂ))⁻¹ = (((2⁻¹ : ℝ)) : ℂ) := by norm_num
    rw [h2c, ← Complex.ofReal_cpow hnn, Real.sqrt_eq_rpow]
    first | norm_num | (congr 1; norm_num) | (congr 1; congr 1; norm_num)
  refine ⟨Real.exp (-(a * Real.sqrt (σ + 1/4))) / (2 * Real.sqrt (σ + 1/4)),
    by positivity, ?_⟩
  unfold shiftedLaplaceHeatKernelC
  rw [hsq]
  rw [show (-(a:ℂ) * ((Real.sqrt (σ + 1/4) : ℝ):ℂ))
      = (((-(a * Real.sqrt (σ + 1/4)) : ℝ)):ℂ) by push_cast; ring]
  rw [← Complex.ofReal_exp]
  push_cast
  field_simp

theorem canonicalPackageTail_uniform_bound_on_halfplane
    (σ : ℝ) (hσ : 0 < σ) (t0 : ℝ) (ht0 : 0 < t0)
    (K : Set ℂ) (hKσ : ∀ s ∈ K, σ ≤ s.re) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
      ‖canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n)) t0 s‖
        ≤ C := by
  obtain ⟨CB, hCB⟩ := B_stage_uniform_bound_on_halfplane (σ/2) (by linarith)
    {((σ:ℝ):ℂ)} (by
      intro s hsmem
      rw [Set.mem_singleton_iff] at hsmem
      rw [hsmem, Complex.ofReal_re]
      linarith)
  refine ⟨CB, fun n s hs => ?_⟩
  have hσs := hKσ s hs
  have hσre : (0:ℝ) < (((σ:ℝ):ℂ)).re := by rw [Complex.ofReal_re]; exact hσ
  have hker : ∀ a : ℝ, 0 ≤ a → ∀ v : ℝ, 0 ≤ v →
      shiftedLaplaceHeatKernelC a ((σ:ℝ):ℂ) = ((v:ℝ):ℂ) →
      ‖kernelTailPart a t0 s‖ ≤ v := by
    intro a hc0 v hv0 hveq
    have hIs : IntegrableOn
        (fun t : ℝ => shiftedHeatIntegrand a s t) (Ioi t0) volume :=
      (shiftedHeatIntegrand_integrableOn a s
        (by linarith)).mono_set (Ioi_subset_Ioi ht0.le)
    have hIσfull : IntegrableOn
        (fun t : ℝ => shiftedHeatIntegrand a ((σ:ℝ):ℂ) t)
        (Ioi (0:ℝ)) volume :=
      shiftedHeatIntegrand_integrableOn a ((σ:ℝ):ℂ) hσre
    have hIσ : IntegrableOn
        (fun t : ℝ => shiftedHeatIntegrand a ((σ:ℝ):ℂ) t)
        (Ioi t0) volume :=
      hIσfull.mono_set (Ioi_subset_Ioi ht0.le)
    have hlap := shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane
      a hc0 ((σ:ℝ):ℂ) hσre
    calc ‖kernelTailPart a t0 s‖
        ≤ ∫ t in Ioi t0, ‖shiftedHeatIntegrand a s t‖ := by
          unfold kernelTailPart
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi t0, ‖shiftedHeatIntegrand a ((σ:ℝ):ℂ) t‖ := by
          apply setIntegral_mono_on hIs.norm hIσ.norm measurableSet_Ioi
          intro t ht
          exact shiftedHeatIntegrand_norm_mono a σ hσs
            (le_of_lt (lt_trans ht0 ht))
      _ ≤ ∫ t in Ioi (0:ℝ), ‖shiftedHeatIntegrand a ((σ:ℝ):ℂ) t‖ := by
          apply setIntegral_mono_set hIσfull.norm
          · filter_upwards with t
            exact norm_nonneg _
          · exact HasSubset.Subset.eventuallyLE (Ioi_subset_Ioi ht0.le)
      _ = ∫ t in Ioi (0:ℝ), (shiftedHeatIntegrand a ((σ:ℝ):ℂ) t).re := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          show ‖shiftedHeatIntegrand a ((σ:ℝ):ℂ) t‖
              = (shiftedHeatIntegrand a ((σ:ℝ):ℂ) t).re
          obtain ⟨r, hr0, hreq⟩ := shiftedHeatIntegrand_at_real a σ t
          rw [hreq, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hr0, Complex.ofReal_re]
      _ = ((∫ t in Ioi (0:ℝ), shiftedHeatIntegrand a ((σ:ℝ):ℂ) t)).re := by
          have h := integral_re hIσfull
          simpa using h
      _ = v := by rw [← hlap, hveq, Complex.ofReal_re]
  have hBσ := hCB n ((σ:ℝ):ℂ) (Set.mem_singleton _)
  have hBform : galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n)
        ((σ:ℝ):ℂ)
      = finiteCanonicalPrimePowerPackage
          (activePrimePowerPairsCenterBelow (admR n))
          shiftedLaplaceHeatKernelC ((σ:ℝ):ℂ) := by
    first | rfl | (unfold finiteCanonicalPrimePowerPackage; rfl) | (congr 1)
  have hterm : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC * kernelTailPart q.center t0 s‖
        ≤ (q.weightC * shiftedLaplaceHeatKernelC q.center ((σ:ℝ):ℂ)).re := by
    intro q _
    have hc0 : (0:ℝ) ≤ q.center := center_nonneg q
    obtain ⟨v, hv0, hveq⟩ := kernel_at_real_point q.center σ hσ
    have hwc : q.weightC = ((q.weightReal : ℝ):ℂ) := by
      first | rfl | simp [PrimePowerPair.weightC]
    have hw0 : (0:ℝ) ≤ q.weightReal := PrimePowerPair.weightReal_nonneg q
    have hkq := hker q.center hc0 v hv0 hveq
    have hlhs : ‖q.weightC * kernelTailPart q.center t0 s‖
        ≤ q.weightReal * v := by
      rw [norm_mul, hwc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_left hkq hw0
    have hrhs : (q.weightC * shiftedLaplaceHeatKernelC q.center ((σ:ℝ):ℂ)).re
        = q.weightReal * v := by
      rw [hwc, hveq]
      rw [show (((q.weightReal:ℝ):ℂ) * ((v:ℝ):ℂ))
          = (((q.weightReal * v : ℝ)):ℂ) by push_cast; ring]
      exact Complex.ofReal_re _
    rw [hrhs]
    exact hlhs
  calc ‖canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n)) t0 s‖
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC * kernelTailPart q.center t0 s‖ := by
        unfold canonicalPackageTail
        exact norm_sum_le _ _
    _ ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          (q.weightC * shiftedLaplaceHeatKernelC q.center ((σ:ℝ):ℂ)).re :=
        Finset.sum_le_sum hterm
    _ = ((∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC * shiftedLaplaceHeatKernelC q.center ((σ:ℝ):ℂ))).re := by
        first
          | (rw [Complex.re_sum])
          | (simp [Complex.re_sum])
          | (exact (Complex.re_sum _ _).symm)
    _ = (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n)
          ((σ:ℝ):ℂ)).re := by
        rw [hBform]
        first | rfl | (unfold finiteCanonicalPrimePowerPackage; rfl)
    _ ≤ ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n)
          ((σ:ℝ):ℂ)‖ := Complex.re_le_norm _
    _ ≤ CB := hBσ

#print axioms shiftedHeatIntegrand_at_real
#print axioms kernel_at_real_point
#print axioms canonicalPackageTail_uniform_bound_on_halfplane

end

end RHFormalization
