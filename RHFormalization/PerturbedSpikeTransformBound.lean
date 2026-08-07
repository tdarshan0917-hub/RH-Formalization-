import RHFormalization.PerturbedSpikeKernelBound
import RHFormalization.CompletedZetaGrowth
import RHFormalization.QuadRemainderTransformGlobal

/-!
# RHFormalization.PerturbedSpikeTransformBound
**Item 2 of 5: the per-q perturbed spike kernel transform bound.**
`∫₀^∞ e^{−δt}·|perturbed(t,a)| dt ≤ (1/π)·Γ(1/2)·δ^{−1/2}
  + Γ(3/2)·δ^{−3/2}·SupV·√2/√π` — the two-leg majorant (heat-sum leg
`t^{−1/2}/(√π·... )` via `sum_heatWeight_le_sqrt` + `sqrt_pi_div_arg`;
Duhamel leg `√t·C₁`) with two Γ-evaluations. Real-transform version
(`e^{−δt}` weight, δ = Re-floor): sufficient for hT since
`‖e^{−st}‖ = e^{−Re s·t} ≤ e^{−δt}`, threaded downstream.
N-free, a-free, qs-uniform.
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

/-- The two-leg pointwise majorant for the perturbed kernel. -/
theorem perturbedSpikeKernel_majorant (qs : Finset ℕ) (hN : 0 < N)
    (t a : ℝ) (ht : 0 < t) :
    |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a|
      ≤ (1 / Real.sqrt Real.pi) * t ^ (-(1/2) : ℝ)
        + (SupVConst * Real.sqrt 2 / Real.sqrt Real.pi) * t ^ ((1/2) : ℝ) := by
  refine le_trans (perturbedSpikeKernel_abs_le qs hN t a ht) (add_le_add ?_ ?_)
  · -- heat leg: (Σ heatWeight)·2 ≤ (√(π/(tπ²))/2)·2 = 1/(√π·√t) = (1/√π)·t^{−1/2}
    have hsum := sum_heatWeight_le_sqrt (N := N) 1 one_pos t ht
    have hkey : Real.sqrt (Real.pi / (t * (Real.pi / 1) ^ 2))
        = 1 / (Real.sqrt Real.pi * Real.sqrt t) := sqrt_pi_div_arg t ht
    have hrpow : t ^ (-(1/2) : ℝ) = 1 / Real.sqrt t := by
      rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow, one_div]
    calc (∑ m : Fin N, heatWeight (N := N) 1 t m) * 2
        ≤ (Real.sqrt (Real.pi / (t * (Real.pi / 1) ^ 2)) / 2) * 2 := by
          apply mul_le_mul_of_nonneg_right hsum (by norm_num)
      _ = Real.sqrt (Real.pi / (t * (Real.pi / 1) ^ 2)) := by ring
      _ = 1 / (Real.sqrt Real.pi * Real.sqrt t) := hkey
      _ = (1 / Real.sqrt Real.pi) * t ^ (-(1/2) : ℝ) := by
          rw [hrpow]
          have hπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
          have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
          field_simp
  · -- Duhamel leg: √t·C/√π = (C/√π)·t^{1/2}
    have hrt : Real.sqrt t = t ^ ((1/2) : ℝ) := Real.sqrt_eq_rpow t
    calc Real.sqrt t * (SupVConst * Real.sqrt 2) / Real.sqrt Real.pi
        = (SupVConst * Real.sqrt 2 / Real.sqrt Real.pi) * Real.sqrt t := by
          ring
      _ = (SupVConst * Real.sqrt 2 / Real.sqrt Real.pi) * t ^ ((1/2) : ℝ) := by
          rw [hrt]

/-- **Item 2: the perturbed-kernel real transform bound.**
For every `δ > 0`: `∫₀^∞ e^{−δt}·|perturbed| ≤ Γ(1/2)·δ^{−1/2}/√π
  + Γ(3/2)·δ^{−3/2}·SupV·√2/√π`. -/
theorem perturbedSpikeKernel_transform_le (qs : Finset ℕ) (hN : 0 < N)
    (a : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in Ioi (0:ℝ), Real.exp (-δ * t)
        * |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a|)
      ≤ (1 / Real.sqrt Real.pi) * (δ ^ (-(1/2):ℝ) * Real.Gamma ((1/2):ℝ))
        + (SupVConst * Real.sqrt 2 / Real.sqrt Real.pi)
            * (δ ^ (-(3/2):ℝ) * Real.Gamma ((3/2):ℝ)) := by
  set C1 : ℝ := 1 / Real.sqrt Real.pi with hC1
  set C2 : ℝ := SupVConst * Real.sqrt 2 / Real.sqrt Real.pi with hC2
  have hSnn : 0 ≤ SupVConst := SupVConst_nonneg_adm
  have hC1nn : 0 ≤ C1 := by rw [hC1]; positivity
  have hC2nn : 0 ≤ C2 := by rw [hC2]; positivity
  -- majorant integrabilities: t^{−1/2}·e^{−δt} and t^{1/2}·e^{−δt} on Ioi 0
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
      C1 * (t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
        + C2 * (t ^ ((1/2):ℝ) * Real.exp (-δ * t))) (Ioi (0:ℝ)) :=
    (hI1.const_mul C1).add (hI2.const_mul C2)
  -- LHS integrand ≤ majorant pointwise on Ioi 0; LHS nonneg integrand
  have hfnn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ Real.exp (-δ * t)
      * |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a| := by
    intro t _
    positivity
  have hfmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-δ * t)
      * |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a|)
      (volume.restrict (Ioi (0:ℝ))) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · fun_prop
    · apply Continuous.abs
      unfold galerkinSpikeKernelPerturbed
      have hmul : Continuous (fun t : ℝ =>
          NormedSpace.exp (t • (-(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1)))
            * galerkinT (N := N) 1 a) := by
        fun_prop
      first
        | exact hmul.matrix_trace
        | exact Continuous.matrix_trace hmul
        | (apply Continuous.matrix_trace; exact hmul)
  have hptw : ∀ t ∈ Ioi (0:ℝ),
      Real.exp (-δ * t)
          * |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a|
        ≤ C1 * (t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
          + C2 * (t ^ ((1/2):ℝ) * Real.exp (-δ * t)) := by
    intro t ht
    have h := perturbedSpikeKernel_majorant qs hN t a ht
    have hexp : (0:ℝ) < Real.exp (-δ * t) := Real.exp_pos _
    calc Real.exp (-δ * t)
          * |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a|
        ≤ Real.exp (-δ * t) * (C1 * t ^ (-(1/2):ℝ) + C2 * t ^ ((1/2):ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hexp.le
          exact h
      _ = C1 * (t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
          + C2 * (t ^ ((1/2):ℝ) * Real.exp (-δ * t)) := by ring
  -- integrate the domination
  have hfInt : IntegrableOn (fun t : ℝ => Real.exp (-δ * t)
      * |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a|)
      (Ioi (0:ℝ)) := by
    refine Integrable.mono' hmajInt hfmeas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnn t ht)]
    exact hptw t ht
  have hmono : (∫ t in Ioi (0:ℝ), Real.exp (-δ * t)
      * |galerkinSpikeKernelPerturbed (N := N) 1 qs ppWeightReal 1 t a|)
      ≤ ∫ t in Ioi (0:ℝ),
          (C1 * (t ^ (-(1/2):ℝ) * Real.exp (-δ * t))
            + C2 * (t ^ ((1/2):ℝ) * Real.exp (-δ * t))) := by
    apply MeasureTheory.setIntegral_mono_on hfInt hmajInt measurableSet_Ioi
    intro t ht
    exact hptw t ht
  refine le_trans hmono (le_of_eq ?_)
  rw [MeasureTheory.integral_add (hI1.const_mul C1) (hI2.const_mul C2)]
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
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hg1, hg2]

#print axioms perturbedSpikeKernel_majorant
#print axioms perturbedSpikeKernel_transform_le

end

end RHFormalization
