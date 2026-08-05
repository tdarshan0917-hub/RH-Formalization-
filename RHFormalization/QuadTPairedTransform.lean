import RHFormalization.QuadTPairedMassBound
import RHFormalization.QuadRemainderTransformGlobal

/-!
# RHFormalization.QuadTPairedTransform
**Ledger item 3c part 4 (final): the T-paired global transform bound.**
`quadTPairedMassFn qs a t := ∫₀ᵗ quadTraceTFn du` is nonneg, continuous,
`≤ t^{3/2}·C'` with `C' = SupV²·√2/√π`; hence its Laplace transform obeys
`‖∫₀^∞ e^{−st}·mass‖ ≤ δ^{−5/2}·Γ(5/2)·C'` for `δ ≤ Re s` — the
items-1/2/2b pipeline verbatim at the new constant. Closes 3c: the
per-prime Duhamel remainder transform is bounded, uniformly in N, qs, a.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory Set intervalIntegral

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The T-paired remainder mass at time `t`. -/
noncomputable def quadTPairedMassFn (qs : Finset ℕ) (a t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, quadTraceTFn (N := N) qs a t u

/-- `t^{3/2}` bound (abs-free: the integrand is nonneg, `t·√t = t^{3/2}`). -/
theorem quadTPairedMassFn_abs_le (qs : Finset ℕ) (hN : 0 < N)
    (a t : ℝ) (ht : 0 < t) :
    |quadTPairedMassFn (N := N) qs a t|
      ≤ t ^ ((3:ℝ)/2) * (SupVConst ^ 2 * Real.sqrt 2 / Real.sqrt Real.pi) := by
  have hnn : 0 ≤ quadTPairedMassFn (N := N) qs a t := by
    unfold quadTPairedMassFn
    apply intervalIntegral.integral_nonneg ht.le
    intro u _
    unfold quadTraceTFn
    exact abs_nonneg _
  rw [abs_of_nonneg hnn]
  have h := quadTPaired_shortTime_mass_le qs hN a t ht
  have hts : t ^ ((3:ℝ)/2) = t * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow]
    rw [show ((3:ℝ)/2) = 1 + (1/2 : ℝ) by norm_num]
    rw [Real.rpow_add ht, Real.rpow_one]
  rw [hts]
  unfold quadTPairedMassFn
  calc (∫ u in (0:ℝ)..t, quadTraceTFn (N := N) qs a t u)
      ≤ t * Real.sqrt t * (SupVConst ^ 2 * Real.sqrt 2) / Real.sqrt Real.pi := h
    _ = t * Real.sqrt t * (SupVConst ^ 2 * Real.sqrt 2 / Real.sqrt Real.pi) := by
        ring

/-- Joint (t,u)-continuity of the T-paired trace (item-1 skeleton + T). -/
theorem continuous_quadTraceTFn_joint (qs : Finset ℕ) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => quadTraceTFn (N := N) qs a p.1 p.2) := by
  unfold quadTraceTFn
  have hF : Continuous (fun p : ℝ × ℝ =>
      quadWordMatrix (N := N) qs p.1 p.2) := by
    unfold quadWordMatrix
    fun_prop
  have hinner : Continuous (fun u : ℝ =>
      ∫ s in (0 : ℝ)..u, quadWordMatrix (N := N) qs u s) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hF continuous_id
  have houter : Continuous (fun p : ℝ × ℝ =>
      (Matrix.diagonal fun m => heatWeight (N := N) 1 (p.1 - p.2) m)) := by
    fun_prop
  have hmul : Continuous (fun p : ℝ × ℝ =>
      (Matrix.diagonal fun m => heatWeight (N := N) 1 (p.1 - p.2) m)
        * ((∫ s in (0 : ℝ)..p.2, quadWordMatrix (N := N) qs p.2 s)
            * galerkinT (N := N) 1 a)) :=
    houter.mul ((hinner.comp continuous_snd).mul continuous_const)
  have htr : Continuous (fun p : ℝ × ℝ =>
      ((Matrix.diagonal fun m => heatWeight (N := N) 1 (p.1 - p.2) m)
        * ((∫ s in (0 : ℝ)..p.2, quadWordMatrix (N := N) qs p.2 s)
            * galerkinT (N := N) 1 a)).trace) := by
    first
      | exact hmul.matrix_trace
      | exact Continuous.matrix_trace hmul
      | (apply Continuous.matrix_trace; exact hmul)
  exact htr.abs

/-- Continuity of the T-paired mass in `t` (parametric lemma). -/
theorem continuous_quadTPairedMassFn (qs : Finset ℕ) (a : ℝ) :
    Continuous (quadTPairedMassFn (N := N) qs a) := by
  unfold quadTPairedMassFn
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (continuous_quadTraceTFn_joint qs a) continuous_id

/-- Transform integrand integrability (items-2b skeleton, constant swapped). -/
theorem quadTPairedTransform_integrableOn (qs : Finset ℕ) (hN : 0 < N)
    (a : ℝ) (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hRe : δ ≤ s.re) :
    IntegrableOn (fun t : ℝ =>
        Complex.exp (-(s * t)) * ((quadTPairedMassFn (N := N) qs a t : ℝ) : ℂ))
      (Ioi (0:ℝ)) := by
  set C : ℝ := SupVConst ^ 2 * Real.sqrt 2 / Real.sqrt Real.pi with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hmajInt : IntegrableOn (fun t : ℝ =>
      t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C) (Ioi (0:ℝ)) :=
    (integrableOn_rpow_exp_majorant hδ).mul_const C
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ =>
        Complex.exp (-(s * t)) * ((quadTPairedMassFn (N := N) qs a t : ℝ) : ℂ))
      (volume.restrict (Ioi (0:ℝ))) := by
    apply Continuous.aestronglyMeasurable
    exact ((Complex.continuous_exp).comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)).mul
      (Complex.continuous_ofReal.comp (continuous_quadTPairedMassFn qs a))
  refine Integrable.mono' hmajInt hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_exp, Complex.norm_real]
  have hre : (-(s * (t:ℂ))).re = -(s.re * t) := by
    simp [Complex.mul_re]
  rw [hre]
  have hker : Real.exp (-(s.re * t)) ≤ Real.exp (-δ * t) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hRe (le_of_lt ht)
    linarith
  have hmass : ‖quadTPairedMassFn (N := N) qs a t‖ ≤ t ^ ((3:ℝ)/2) * C := by
    rw [Real.norm_eq_abs]
    exact quadTPairedMassFn_abs_le qs hN a t ht
  calc Real.exp (-(s.re * t)) * ‖quadTPairedMassFn (N := N) qs a t‖
      ≤ Real.exp (-δ * t) * (t ^ ((3:ℝ)/2) * C) :=
        mul_le_mul hker hmass (norm_nonneg _) (Real.exp_pos _).le
    _ = t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C := by ring

/-- **3c COMPLETE: the per-prime T-paired remainder transform bound.**
Uniform in N, qs, a; `δ ≤ Re s`. -/
theorem quadTPaired_transform_global_le (qs : Finset ℕ) (hN : 0 < N)
    (a : ℝ) (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hRe : δ ≤ s.re) :
    ‖∫ t in Ioi (0:ℝ),
        Complex.exp (-(s * t)) * ((quadTPairedMassFn (N := N) qs a t : ℝ) : ℂ)‖
      ≤ δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2)
          * (SupVConst ^ 2 * Real.sqrt 2 / Real.sqrt Real.pi) := by
  set C : ℝ := SupVConst ^ 2 * Real.sqrt 2 / Real.sqrt Real.pi with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hpt : ∀ t ∈ Ioi (0:ℝ),
      ‖Complex.exp (-(s * t)) * ((quadTPairedMassFn (N := N) qs a t : ℝ) : ℂ)‖
        ≤ t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C := by
    intro t ht
    rw [norm_mul, Complex.norm_exp, Complex.norm_real]
    have hre : (-(s * (t:ℂ))).re = -(s.re * t) := by
      simp [Complex.mul_re]
    rw [hre]
    have hker : Real.exp (-(s.re * t)) ≤ Real.exp (-δ * t) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hRe (le_of_lt ht)
      linarith
    have hmass : ‖quadTPairedMassFn (N := N) qs a t‖ ≤ t ^ ((3:ℝ)/2) * C := by
      rw [Real.norm_eq_abs]
      exact quadTPairedMassFn_abs_le qs hN a t ht
    calc Real.exp (-(s.re * t)) * ‖quadTPairedMassFn (N := N) qs a t‖
        ≤ Real.exp (-δ * t) * (t ^ ((3:ℝ)/2) * C) :=
          mul_le_mul hker hmass (norm_nonneg _) (Real.exp_pos _).le
      _ = t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C := by ring
  have hmajInt : IntegrableOn (fun t : ℝ =>
      t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C) (Ioi (0:ℝ)) :=
    (integrableOn_rpow_exp_majorant hδ).mul_const C
  have hbound : ‖∫ t in Ioi (0:ℝ),
      Complex.exp (-(s * t)) * ((quadTPairedMassFn (N := N) qs a t : ℝ) : ℂ)‖
      ≤ ∫ t in Ioi (0:ℝ), t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C := by
    refine MeasureTheory.norm_integral_le_of_norm_le hmajInt ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hpt t ht
  refine hbound.trans (le_of_eq ?_)
  have hgamma : ∫ t in Ioi (0:ℝ), t ^ ((3:ℝ)/2) * Real.exp (-δ * t)
      = δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2) := by
    have h := integral_rpow_mul_exp_eq_gamma
      (a := (5:ℝ)/2) (b := δ) (by norm_num) hδ
    rw [show ((5:ℝ)/2 - 1) = (3:ℝ)/2 by norm_num] at h
    rw [h]
    congr 1
    rw [show (-(5:ℝ)/2) = -((5:ℝ)/2) by norm_num]
  calc ∫ t in Ioi (0:ℝ), t ^ ((3:ℝ)/2) * Real.exp (-δ * t) * C
      = (∫ t in Ioi (0:ℝ), t ^ ((3:ℝ)/2) * Real.exp (-δ * t)) * C := by
        first
          | exact MeasureTheory.integral_mul_const _ C
          | exact integral_mul_const _ C
          | rw [MeasureTheory.integral_mul_const]
          | rw [integral_mul_const]
    _ = δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2) * C := by rw [hgamma]

#print axioms quadTPairedMassFn_abs_le
#print axioms continuous_quadTPairedMassFn
#print axioms quadTPairedTransform_integrableOn
#print axioms quadTPaired_transform_global_le

end

end RHFormalization
