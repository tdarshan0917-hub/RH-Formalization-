-- SENTINEL: SHORT-v3
import RHFormalization.AdaptiveSectorObjects
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCore
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreSummability
import Mathlib

/-!
# AdaptiveShortSectorBound v2 — the Short row (h_short_le)

v1→v2: name fixes only (Complex.norm_real + Real.norm_eq_abs;
sum_le_tsum root-namespace; IsCompact.exists_bound_of_continuousOn
replaces the maximum extraction) and the linarith atom repair
(hC restated with the `-a^2/(4t)` atoms the goal actually contains).
Mechanism unchanged: reference-spike domination on (0,t0], Gaussian
center decay, banked envelope summability, partial ≤ tsum.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

/-- Reference short-time mass: `∫₀^{t0} ‖shiftedHeatIntegrand 0 1 t‖`. -/
def shortRefMass (t0 : ℝ) : ℝ :=
  ∫ t in Ioc (0:ℝ) t0, ‖shiftedHeatIntegrand 0 1 t‖

theorem shortRefMass_nonneg (t0 : ℝ) : 0 ≤ shortRefMass t0 := by
  unfold shortRefMass
  exact MeasureTheory.integral_nonneg (fun t => norm_nonneg _)

/-- Exact norm of the shifted heat integrand for `t > 0`. -/
theorem shiftedHeatIntegrand_norm_eq (a : ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖shiftedHeatIntegrand a s t‖
      = Real.exp (-(s.re) * t) * Real.exp (-(t/4))
        * ((1 : ℝ) / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t))) := by
  have h3 : (0:ℝ) ≤ (1 : ℝ) / Real.sqrt (4 * Real.pi * t)
      * Real.exp (-(a ^ 2) / (4 * t)) := by positivity
  unfold shiftedHeatIntegrand heatKernelG
  have hcast : -(t:ℂ)/4 = ((-(t/4) : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_mul, hcast]
  first
    | (simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero])
    | (simp only [Complex.norm_eq_abs, Complex.abs_exp, Complex.mul_re, Complex.neg_re,
        Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero])
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h3]
  try ring

/-- **Per-spike short bound**: Gaussian center decay, uniform on
`Re s ≥ −σ0`. -/
theorem kernelShortPart_norm_le (a t0 sigma0 : ℝ) (ht0 : 0 < t0)
    (hsig : 0 ≤ sigma0) {s : ℂ} (hsre : -sigma0 ≤ s.re) :
    ‖kernelShortPart a t0 s‖
      ≤ Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4) * shortRefMass t0
        * Real.exp (-(a ^ 2) / (4 * t0)) := by
  have hint_a : IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a s t)
      (Ioc (0:ℝ) t0) volume := shiftedHeatIntegrand_integrableOn_Ioc a s t0 ht0
  have hint_ref : IntegrableOn (fun t : ℝ => shiftedHeatIntegrand 0 1 t)
      (Ioc (0:ℝ) t0) volume := shiftedHeatIntegrand_integrableOn_Ioc 0 1 t0 ht0
  have hpt : ∀ t ∈ Ioc (0:ℝ) t0,
      ‖shiftedHeatIntegrand a s t‖
        ≤ (Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4)
            * Real.exp (-(a ^ 2) / (4 * t0))) * ‖shiftedHeatIntegrand 0 1 t‖ := by
    intro t htmem
    obtain ⟨ht1, ht2⟩ := htmem
    have href : ‖shiftedHeatIntegrand 0 1 t‖
        = Real.exp (-t) * Real.exp (-(t/4))
          * ((1 : ℝ) / Real.sqrt (4 * Real.pi * t)) := by
      rw [shiftedHeatIntegrand_norm_eq 0 1 ht1]
      first
        | norm_num
        | simp
        | (norm_num [Real.exp_zero])
    rw [shiftedHeatIntegrand_norm_eq a s ht1, href]
    have hD : (0:ℝ) ≤ (1 : ℝ) / Real.sqrt (4 * Real.pi * t) := by positivity
    have hC : a ^ 2 / (4 * t0) ≤ a ^ 2 / (4 * t) := by
      first
        | (rw [div_le_div_iff (by linarith) (by linarith)]
           nlinarith [sq_nonneg a, ht1, ht2])
        | exact div_le_div_of_nonneg_left (sq_nonneg a) (by linarith) (by linarith)
        | (gcongr <;> linarith)
    have hC' : -a ^ 2 / (4 * t) ≤ -a ^ 2 / (4 * t0) := by
      rw [neg_div, neg_div]
      exact neg_le_neg hC
    have hA : -sigma0 * t ≤ s.re * t := mul_le_mul_of_nonneg_right hsre ht1.le
    have hB : sigma0 * t ≤ sigma0 * t0 := mul_le_mul_of_nonneg_left ht2 hsig
    have hexp : Real.exp (-(s.re) * t) * Real.exp (-(t/4))
          * Real.exp (-(a ^ 2) / (4 * t))
        ≤ Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4)
            * Real.exp (-(a ^ 2) / (4 * t0))
          * (Real.exp (-t) * Real.exp (-(t/4))) := by
      simp only [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hA, hB, hC', ht1, ht2, ht0]
    calc Real.exp (-(s.re) * t) * Real.exp (-(t/4))
          * ((1 : ℝ) / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t)))
        = (Real.exp (-(s.re) * t) * Real.exp (-(t/4))
            * Real.exp (-(a ^ 2) / (4 * t)))
          * ((1 : ℝ) / Real.sqrt (4 * Real.pi * t)) := by ring
      _ ≤ (Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4)
            * Real.exp (-(a ^ 2) / (4 * t0))
            * (Real.exp (-t) * Real.exp (-(t/4))))
          * ((1 : ℝ) / Real.sqrt (4 * Real.pi * t)) :=
        mul_le_mul_of_nonneg_right hexp hD
      _ = (Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4)
            * Real.exp (-(a ^ 2) / (4 * t0)))
          * (Real.exp (-t) * Real.exp (-(t/4))
            * ((1 : ℝ) / Real.sqrt (4 * Real.pi * t))) := by ring
  calc ‖kernelShortPart a t0 s‖
      ≤ ∫ t in Ioc (0:ℝ) t0, ‖shiftedHeatIntegrand a s t‖ := by
        unfold kernelShortPart
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc (0:ℝ) t0,
          (Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4)
            * Real.exp (-(a ^ 2) / (4 * t0))) * ‖shiftedHeatIntegrand 0 1 t‖ := by
        first
          | exact MeasureTheory.setIntegral_mono_on hint_a.norm
              (hint_ref.norm.const_mul _) measurableSet_Ioc hpt
          | exact MeasureTheory.set_integral_mono_on hint_a.norm
              (hint_ref.norm.const_mul _) measurableSet_Ioc hpt
    _ = (Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4)
          * Real.exp (-(a ^ 2) / (4 * t0))) * shortRefMass t0 := by
        unfold shortRefMass
        first
          | exact MeasureTheory.integral_const_mul _ _
          | rw [MeasureTheory.integral_const_mul]
          | exact MeasureTheory.integral_mul_left _ _
    _ = Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4) * shortRefMass t0
          * Real.exp (-(a ^ 2) / (4 * t0)) := by ring

/-- **Summed short bound**: n-uniform via partial ≤ tsum on the banked
Gaussian envelope. -/
theorem canonicalPackageShort_norm_le
    (I : Finset PrimePowerPair) (t0 sigma0 : ℝ) (ht0 : 0 < t0)
    (hsig : 0 ≤ sigma0) {s : ℂ} (hsre : -sigma0 ≤ s.re) :
    ‖canonicalPackageShort I t0 s‖
      ≤ Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4) * shortRefMass t0
        * (∑' q, heatKernelGaussianCoreEnvelope t0 q) := by
  have hC0nn : 0 ≤ Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4)
      * shortRefMass t0 :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (shortRefMass_nonneg t0)
  have henv_nonneg : ∀ q, 0 ≤ heatKernelGaussianCoreEnvelope t0 q := by
    intro q
    first
      | exact heatKernelGaussianCoreEnvelope_nonneg t0 q
      | (simp only [heatKernelGaussianCoreEnvelope]; positivity)
  have hsummable : Summable (heatKernelGaussianCoreEnvelope t0) :=
    heatKernelGaussianCoreEnvelope_summable t0 ht0
  calc ‖canonicalPackageShort I t0 s‖
      ≤ ∑ q ∈ I, ‖q.weightC * kernelShortPart q.center t0 s‖ := by
        unfold canonicalPackageShort
        exact norm_sum_le _ _
    _ = ∑ q ∈ I, ‖q.weightC‖ * ‖kernelShortPart q.center t0 s‖ := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [norm_mul]
    _ ≤ ∑ q ∈ I, ‖q.weightC‖
          * (Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4) * shortRefMass t0
            * Real.exp (-(q.center ^ 2) / (4 * t0))) := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact mul_le_mul_of_nonneg_left
          (kernelShortPart_norm_le q.center t0 sigma0 ht0 hsig hsre)
          (norm_nonneg _)
    _ = (Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4) * shortRefMass t0)
          * ∑ q ∈ I, heatKernelGaussianCoreEnvelope t0 q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [heatKernelGaussianCoreEnvelope]
        ring
    _ ≤ (Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4) * shortRefMass t0)
          * (∑' q, heatKernelGaussianCoreEnvelope t0 q) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0nn
        first
          | exact sum_le_tsum I (fun q _ => henv_nonneg q) hsummable
          | exact hsummable.sum_le_tsum I (fun q _ => henv_nonneg q)
          | exact Finset.sum_le_tsum I (fun q _ => henv_nonneg q) hsummable
    _ = Real.exp (sigma0 * t0) * Real.exp (5 * t0 / 4) * shortRefMass t0
          * (∑' q, heatKernelGaussianCoreEnvelope t0 q) := by ring

/-- **THE SHORT ROW — h_short_le in the combiner's exact shape.** -/
theorem adaptiveSectorShort_loc_bdd (t0 : ℝ) (ht0 : 0 < t0) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Cl : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖adaptiveSectorShort t0 n s‖ ≤ Cl := by
  intro K hK _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖x‖ ≤ C := by
    first
      | exact hK.exists_bound_of_continuousOn continuousOn_id
      | exact hK.exists_bound_of_continuousOn continuous_id.continuousOn
      | (obtain ⟨C, hC⟩ := (hK.image continuous_norm).isBounded.subset_ball 0
         exact ⟨C, fun x hx => by
           have := hC (Set.mem_image_of_mem _ hx)
           simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg x)] using
             le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using this)⟩)
  refine ⟨Real.exp (max C 0 * t0) * Real.exp (5 * t0 / 4) * shortRefMass t0
      * (∑' q, heatKernelGaussianCoreEnvelope t0 q), ?_⟩
  intro n s hs
  have hsig : (0:ℝ) ≤ max C 0 := le_max_right _ _
  have hsre : -(max C 0) ≤ s.re := by
    have h1 : ‖s‖ ≤ C := hC s hs
    have h2 : |s.re| ≤ ‖s‖ := by
      first
        | exact Complex.abs_re_le_norm s
        | exact Complex.abs_re_le_abs s
        | exact abs_re_le_norm s
    have h3 : -‖s‖ ≤ s.re := neg_le_of_abs_le h2
    have h4 : C ≤ max C 0 := le_max_left _ _
    linarith
  have hpack := canonicalPackageShort_norm_le
    (activePrimePowerPairsCenterBelow (admR n)) t0 (max C 0) ht0 hsig hsre
  unfold adaptiveSectorShort
  exact hpack

#print axioms shiftedHeatIntegrand_norm_eq
#print axioms kernelShortPart_norm_le
#print axioms canonicalPackageShort_norm_le
#print axioms adaptiveSectorShort_loc_bdd

end

end RHFormalization
