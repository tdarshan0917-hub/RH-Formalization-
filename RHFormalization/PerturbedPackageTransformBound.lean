import RHFormalization.PerturbedSpikeTransformBound
import RHFormalization.AdaptiveGalerkinStage

/-!
# RHFormalization.PerturbedPackageTransformBound
**Item 3 of 5: the q-summed perturbed package transform bound.**
Time-domain: `|galerkinOneLetterPerturbedRaw(t)| ≤ mass(qs,w)·(perturbed
kernel bound)` since the per-q bound is displacement-free. Transform:
one application of the item-2 pipeline at the summed constant. At the
adaptive stage with the `1/(2L) = e^{−R}/2` normalization:
`e^{−R/2}`-crushed. N-free.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory Set

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Pointwise: the raw package is mass-dominated by the kernel bound. -/
theorem oneLetterPerturbedRaw_abs_le (qs : Finset ℕ) (hN : 0 < N)
    (t : ℝ) (ht : 0 < t) :
    |galerkinOneLetterPerturbedRaw (N := N) 1 qs ppWeightReal 1 t|
      ≤ (∑ q ∈ qs, |ppWeightReal q|)
        * ((∑ m : Fin N, heatWeight (N := N) 1 t m) * 2
            + Real.sqrt t * (SupVConst * Real.sqrt 2) / Real.sqrt Real.pi) := by
  unfold galerkinOneLetterPerturbedRaw
  set B : ℝ := (∑ m : Fin N, heatWeight (N := N) 1 t m) * 2
      + Real.sqrt t * (SupVConst * Real.sqrt 2) / Real.sqrt Real.pi with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    have hSnn : 0 ≤ SupVConst := SupVConst_nonneg_adm
    have hh : ∀ m : Fin N, 0 ≤ heatWeight (N := N) 1 t m := by
      intro m
      unfold heatWeight
      exact le_of_lt (Real.exp_pos _)
    have hsum : 0 ≤ ∑ m : Fin N, heatWeight (N := N) 1 t m :=
      Finset.sum_nonneg (fun m _ => hh m)
    positivity
  calc |∑ q ∈ qs, ppWeightReal q
        * galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t (Real.log q)|
      ≤ ∑ q ∈ qs, |ppWeightReal q
          * galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t (Real.log q)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ qs, |ppWeightReal q| * B := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [hB]
        exact perturbedSpikeKernel_abs_le qs hN t (Real.log q) ht
    _ = (∑ q ∈ qs, |ppWeightReal q|) * B := by
        rw [← Finset.sum_mul]

/-- **Item 3: the transform of the raw perturbed package.**
`∫₀^∞ e^{−δt}·|Raw(t)| ≤ mass·(Γ(1/2)δ^{−1/2}/√π + Γ(3/2)δ^{−3/2}·SupV√2/√π)`. -/
theorem oneLetterPerturbedRaw_transform_le (qs : Finset ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in Ioi (0:ℝ), Real.exp (-δ * t)
        * |galerkinOneLetterPerturbedRaw (N := N) 1 qs ppWeightReal 1 t|)
      ≤ (∑ q ∈ qs, |ppWeightReal q|)
        * ((1 / Real.sqrt Real.pi) * (δ ^ (-(1/2):ℝ) * Real.Gamma ((1/2):ℝ))
          + (SupVConst * Real.sqrt 2 / Real.sqrt Real.pi)
              * (δ ^ (-(3/2):ℝ) * Real.Gamma ((3/2):ℝ))) := by
  set W : ℝ := ∑ q ∈ qs, |ppWeightReal q| with hW
  have hWnn : 0 ≤ W := Finset.sum_nonneg (fun q _ => abs_nonneg _)
  set C1 : ℝ := 1 / Real.sqrt Real.pi with hC1
  set C2 : ℝ := SupVConst * Real.sqrt 2 / Real.sqrt Real.pi with hC2
  have hSnn : 0 ≤ SupVConst := SupVConst_nonneg_adm
  have hC1nn : 0 ≤ C1 := by rw [hC1]; positivity
  have hC2nn : 0 ≤ C2 := by rw [hC2]; positivity
  have hI1 : IntegrableOn (fun t : ℝ => t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
      (Ioi (0:ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := (-(1/2):ℝ)) (b := δ) (by norm_num) (by norm_num) hδ
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
  have hI2 : IntegrableOn (fun t : ℝ => t ^ ((1/2):ℝ) * Real.exp (-δ * t))
      (Ioi (0:ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := ((1/2):ℝ)) (b := δ) (by norm_num) (by norm_num) hδ
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
  have hmajInt : IntegrableOn (fun t : ℝ =>
      W * (C1 * (t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
        + C2 * (t ^ ((1/2):ℝ) * Real.exp (-δ * t)))) (Ioi (0:ℝ)) :=
    ((hI1.const_mul C1).add (hI2.const_mul C2)).const_mul W
  have hfmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-δ * t)
      * |galerkinOneLetterPerturbedRaw (N := N) 1 qs ppWeightReal 1 t|)
      (volume.restrict (Ioi (0:ℝ))) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · fun_prop
    · apply Continuous.abs
      unfold galerkinOneLetterPerturbedRaw
      apply continuous_finset_sum
      intro q _
      apply Continuous.mul continuous_const
      unfold galerkinSpikeKernelPerturbed
      have hmul : Continuous (fun t : ℝ =>
          NormedSpace.exp (t • (-(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1)))
            * galerkinT (N := N) 1 (Real.log q)) := by
        fun_prop
      first
        | exact hmul.matrix_trace
        | exact Continuous.matrix_trace hmul
        | (apply Continuous.matrix_trace; exact hmul)
  have hptw : ∀ t ∈ Ioi (0:ℝ),
      Real.exp (-δ * t)
          * |galerkinOneLetterPerturbedRaw (N := N) 1 qs ppWeightReal 1 t|
        ≤ W * (C1 * (t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
            + C2 * (t ^ ((1/2):ℝ) * Real.exp (-δ * t))) := by
    intro t ht
    have hexp : (0:ℝ) < Real.exp (-δ * t) := Real.exp_pos _
    have hraw := oneLetterPerturbedRaw_abs_le qs hN t ht
    have hmaj := perturbedSpikeKernel_majorant qs hN t 0 ht
    -- kernel bound → rpow majorant (a-free: reuse the majorant shape)
    have hker : (∑ m : Fin N, heatWeight (N := N) 1 t m) * 2
          + Real.sqrt t * (SupVConst * Real.sqrt 2) / Real.sqrt Real.pi
        ≤ C1 * t ^ (-(1/2):ℝ) + C2 * t ^ ((1/2):ℝ) := by
      refine add_le_add ?_ ?_
      · have hsum := sum_heatWeight_le_sqrt (N := N) 1 one_pos t ht
        have hkey : Real.sqrt (Real.pi / (t * (Real.pi / 1) ^ 2))
            = 1 / (Real.sqrt Real.pi * Real.sqrt t) := sqrt_pi_div_arg t ht
        have hrpow : t ^ (-(1/2) : ℝ) = 1 / Real.sqrt t := by
          rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow, one_div]
        calc (∑ m : Fin N, heatWeight (N := N) 1 t m) * 2
            ≤ (Real.sqrt (Real.pi / (t * (Real.pi / 1) ^ 2)) / 2) * 2 := by
              apply mul_le_mul_of_nonneg_right hsum (by norm_num)
          _ = Real.sqrt (Real.pi / (t * (Real.pi / 1) ^ 2)) := by ring
          _ = 1 / (Real.sqrt Real.pi * Real.sqrt t) := hkey
          _ = C1 * t ^ (-(1/2) : ℝ) := by
              rw [hrpow, hC1]
              have hπ : (0:ℝ) < Real.sqrt Real.pi :=
                Real.sqrt_pos.mpr Real.pi_pos
              have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
              field_simp
      · have hrt : Real.sqrt t = t ^ ((1/2) : ℝ) := Real.sqrt_eq_rpow t
        calc Real.sqrt t * (SupVConst * Real.sqrt 2) / Real.sqrt Real.pi
            = C2 * Real.sqrt t := by rw [hC2]; ring
          _ = C2 * t ^ ((1/2) : ℝ) := by rw [hrt]
    calc Real.exp (-δ * t)
          * |galerkinOneLetterPerturbedRaw (N := N) 1 qs ppWeightReal 1 t|
        ≤ Real.exp (-δ * t)
            * (W * (C1 * t ^ (-(1/2):ℝ) + C2 * t ^ ((1/2):ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hexp.le
          refine le_trans hraw ?_
          exact mul_le_mul_of_nonneg_left hker hWnn
      _ = W * (C1 * (t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
          + C2 * (t ^ ((1/2):ℝ) * Real.exp (-δ * t))) := by ring
  have hfInt : IntegrableOn (fun t : ℝ => Real.exp (-δ * t)
      * |galerkinOneLetterPerturbedRaw (N := N) 1 qs ppWeightReal 1 t|)
      (Ioi (0:ℝ)) := by
    refine Integrable.mono' hmajInt hfmeas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hptw t ht
  have hmono : (∫ t in Ioi (0:ℝ), Real.exp (-δ * t)
      * |galerkinOneLetterPerturbedRaw (N := N) 1 qs ppWeightReal 1 t|)
      ≤ ∫ t in Ioi (0:ℝ),
          W * (C1 * (t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
            + C2 * (t ^ ((1/2):ℝ) * Real.exp (-δ * t))) := by
    apply MeasureTheory.setIntegral_mono_on hfInt hmajInt measurableSet_Ioi
    intro t ht
    exact hptw t ht
  refine le_trans hmono (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hI1.const_mul C1) (hI2.const_mul C2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hg1 : ∫ t in Ioi (0:ℝ), t ^ (-(1/2):ℝ) * Real.exp (-δ * t)
      = δ ^ (-(1/2):ℝ) * Real.Gamma ((1/2):ℝ) := by
    have h := integral_rpow_mul_exp_eq_gamma
      (a := ((1/2):ℝ)) (b := δ) (by norm_num) hδ
    rw [show ((1/2):ℝ) - 1 = (-(1/2):ℝ) by norm_num] at h
    rw [h]
  have hg2 : ∫ t in Ioi (0:ℝ), t ^ ((1/2):ℝ) * Real.exp (-δ * t)
      = δ ^ (-(3/2):ℝ) * Real.Gamma ((3/2):ℝ) := by
    have h := integral_rpow_mul_exp_eq_gamma
      (a := ((3/2):ℝ)) (b := δ) (by norm_num) hδ
    rw [show ((3/2):ℝ) - 1 = ((1/2):ℝ) by norm_num] at h
    rw [h]
    congr 1
    norm_num
  rw [hg1, hg2]

#print axioms oneLetterPerturbedRaw_abs_le
#print axioms oneLetterPerturbedRaw_transform_le

end

end RHFormalization
