import RHFormalization.DA2LaplaceResolvent
import Mathlib

/-!
# LaplaceTSquaredKit — `∫₀^∞ t·e^{−at} dt = a⁻²` for Re a > 0

ROUTE CARD
1. Target: the power-1 sibling of the repo's own `integral_cexp_neg_mul_Ioi`
   (DA2LaplaceResolvent). FTC route on Ioi: antiderivative
   `F t = −(t/a + 1/a²)·e^{−at}`, `F' t = t·e^{−at}`, `F 0 = −a⁻²`, `F → 0`
   (poly beats exp), via `integral_Ioi_of_hasDerivAt_of_tendsto`.
2. Raw B on Ω? NO. B−M bare Prop? NO — a pure Mathlib integral.
3. Consumer: PerturbedFStageM2Split — Laplace of the c₁ profile term
   `t·Σ V_mm e^{−tλ_m} → Σ V_mm (s+λ_m)⁻²` (the squared-resolvent
   one-letter profile of the s-side M=2 identity).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set

/-- The antiderivative of `t·e^{−at}`. -/
private noncomputable def lapT (a : ℂ) (t : ℝ) : ℂ :=
  -((t : ℂ) / a + 1 / a ^ 2) * Complex.exp (-a * (t : ℂ))

private theorem lapT_hasDerivAt {a : ℂ} (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (lapT a) ((t : ℂ) * Complex.exp (-a * (t : ℂ))) t := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t))
  have h1 : HasDerivAt (fun x : ℝ => ((x : ℂ)) * a⁻¹) (1 * a⁻¹) t :=
    hcast.mul_const a⁻¹
  have h2 : HasDerivAt (fun x : ℝ => ((x : ℂ)) * a⁻¹ + 1 / a ^ 2)
      (1 * a⁻¹) t := h1.add_const _
  have h3 : HasDerivAt (fun x : ℝ => -(((x : ℂ)) * a⁻¹ + 1 / a ^ 2))
      (-(1 * a⁻¹)) t := h2.neg
  have hin : HasDerivAt (fun x : ℝ => -a * (x : ℂ)) (-a * 1) t :=
    hcast.const_mul (-a)
  have h4 : HasDerivAt (fun x : ℝ => Complex.exp (-a * (x : ℂ)))
      (Complex.exp (-a * (t : ℂ)) * (-a * 1)) t := hin.cexp
  have hmul : HasDerivAt
      (fun x : ℝ =>
        -(((x : ℂ)) * a⁻¹ + 1 / a ^ 2) * Complex.exp (-a * (x : ℂ)))
      (-(1 * a⁻¹) * Complex.exp (-a * (t : ℂ))
        + -(((t : ℂ)) * a⁻¹ + 1 / a ^ 2)
            * (Complex.exp (-a * (t : ℂ)) * (-a * 1))) t := h3.mul h4
  have hfun : (fun x : ℝ =>
      -(((x : ℂ)) * a⁻¹ + 1 / a ^ 2) * Complex.exp (-a * (x : ℂ)))
      = lapT a := by
    funext x
    unfold lapT
    ring
  have hder : -(1 * a⁻¹) * Complex.exp (-a * (t : ℂ))
      + -(((t : ℂ)) * a⁻¹ + 1 / a ^ 2)
          * (Complex.exp (-a * (t : ℂ)) * (-a * 1))
      = (t : ℂ) * Complex.exp (-a * (t : ℂ)) := by
    field_simp
    ring
  rw [hfun, hder] at hmul
  exact hmul

private theorem lapT_tendsto_zero {a : ℂ} (ha : 0 < a.re) :
    Filter.Tendsto (lapT a) Filter.atTop (nhds 0) := by
  have hnorm : ∀ t : ℝ, 0 ≤ t →
      ‖lapT a t‖ ≤ (t / ‖a‖ + 1 / ‖a‖ ^ 2) * Real.exp (-(a.re) * t) := by
    intro t ht
    have habs : ‖Complex.exp (-a * (t : ℂ))‖ = Real.exp (-(a.re) * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hA : ‖-(((t : ℂ)) / a + 1 / a ^ 2)‖ ≤ t / ‖a‖ + 1 / ‖a‖ ^ 2 := by
      rw [norm_neg]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖((t : ℂ)) / a‖ = t / ‖a‖ := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht]
      have h2 : ‖(1 : ℂ) / a ^ 2‖ = 1 / ‖a‖ ^ 2 := by
        rw [norm_div, norm_one, norm_pow]
      rw [h1, h2]
    calc ‖lapT a t‖
        = ‖-(((t : ℂ)) / a + 1 / a ^ 2)‖ * ‖Complex.exp (-a * (t : ℂ))‖ := by
          rw [lapT, norm_mul]
      _ ≤ (t / ‖a‖ + 1 / ‖a‖ ^ 2) * Real.exp (-(a.re) * t) := by
          rw [habs]
          exact mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
  have hbound : Filter.Tendsto
      (fun t : ℝ => (t / ‖a‖ + 1 / ‖a‖ ^ 2) * Real.exp (-(a.re) * t))
      Filter.atTop (nhds 0) := by
    have ht1 : Filter.Tendsto (fun t : ℝ => (t / ‖a‖) * Real.exp (-(a.re) * t))
        Filter.atTop (nhds 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a.re ha
      have hcongr : ∀ᶠ t : ℝ in Filter.atTop,
          t ^ (1:ℝ) * Real.exp (-a.re * t) * (1 / ‖a‖)
            = (t / ‖a‖) * Real.exp (-(a.re) * t) := by
        filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
        rw [Real.rpow_one]
        ring_nf
      have := (h.mul_const (1 / ‖a‖))
      simpa using Filter.Tendsto.congr' hcongr (by simpa using this)
    have ht2 : Filter.Tendsto (fun t : ℝ => (1 / ‖a‖ ^ 2) * Real.exp (-(a.re) * t))
        Filter.atTop (nhds 0) := by
      have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-(a.re) * t))
          Filter.atTop (nhds 0) := by
        have harg : Filter.Tendsto (fun t : ℝ => -(a.re) * t)
            Filter.atTop Filter.atBot := by
          first
            | exact tendsto_id.const_mul_atTop_of_neg (by linarith)
            | exact Filter.Tendsto.const_mul_atTop_of_neg (by linarith) Filter.tendsto_id
            | (have h2 := Filter.tendsto_id.atTop_mul_neg_const (r := -(a.re)) (by linarith)
               simpa [mul_comm] using h2)
            | (have h2 := (Filter.tendsto_id (α := ℝ)).atTop_mul_neg_const
                 (C := -(a.re)) (by linarith)
               simpa [mul_comm] using h2)
        exact Real.tendsto_exp_atBot.comp harg
      have h := hexp.const_mul (1 / ‖a‖ ^ 2)
      simpa using h
    have hsum := ht1.add ht2
    simpa [add_mul] using hsum
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
  exact hnorm t ht

private theorem integrableOn_t_cexp {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-a * (t : ℂ)))
      (Ioi (0:ℝ)) := by
  have hreal : IntegrableOn (fun t : ℝ => t * Real.exp (-(a.re * t)))
      (Ioi (0:ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := a.re) (by norm_num) le_rfl ha
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) * Complex.exp (-a * (t : ℂ)))
      (volume.restrict (Ioi (0:ℝ))) := by
    apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal).mul
      ((Complex.continuous_exp).comp
        ((continuous_const.mul Complex.continuous_ofReal)))
  refine ⟨hmeas, ?_⟩
  have hfin := hreal.2
  refine hfin.mono ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  have habs : ‖Complex.exp (-a * (t : ℂ))‖ = Real.exp (-(a.re) * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, habs]
  rw [Real.norm_of_nonneg (by positivity)]
  rw [neg_mul]

/-- **The t-kit**: `∫₀^∞ t·e^{−at} dt = a⁻²` for Re a > 0. -/
theorem integral_t_cexp_neg_mul_Ioi {a : ℂ} (ha : 0 < a.re) :
    (∫ t in Set.Ioi (0:ℝ), (t : ℂ) * Complex.exp (-a * (t : ℂ))) = (a ^ 2)⁻¹ := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := lapT a)
    (f' := fun t : ℝ => (t : ℂ) * Complex.exp (-a * (t : ℂ)))
    (a := (0:ℝ))
    ((lapT_hasDerivAt ha0 0).continuousAt.continuousWithinAt)
    (fun t ht => lapT_hasDerivAt ha0 t)
    ((integrableOn_t_cexp ha).mono_set (by simp))
    (lapT_tendsto_zero ha)
  rw [hFTC]
  unfold lapT
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_div]
  field_simp
  ring

/-- D.A2 power-1 termwise: `(s+λ)⁻² = ∫₀^∞ t·e^{−(s+λ)t} dt`, Re s > 0, λ ≥ 0. -/
theorem sq_inv_eq_laplace_t_exp (s : ℂ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hs : 0 < s.re) :
    ((s + (lam : ℂ)) ^ 2)⁻¹
      = ∫ t in Set.Ioi (0:ℝ),
          (t : ℂ) * Complex.exp (-(s + (lam : ℂ)) * (t : ℂ)) := by
  have hre : 0 < (s + (lam : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith
  rw [integral_t_cexp_neg_mul_Ioi hre]

#print axioms integral_t_cexp_neg_mul_Ioi
#print axioms sq_inv_eq_laplace_t_exp

end

end RHFormalization
