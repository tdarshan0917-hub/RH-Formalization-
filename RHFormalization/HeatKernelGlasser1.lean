import RHFormalization.HeatKernelLaplaceBase
import Mathlib

/-!
# HeatKernelGlasser1 — Glasser substitution, step 1 (B-side connector, brick 1a)

ROUTE CARD
1. Target: brick 1a of the B-side connector (the last classical input,
   BSideHeatKernelLaplace sorry). Glasser route to
   ∫₀^∞ e^{−p²u²−q²/u²} du = (√π/2p)·e^{−2pq}.
2. This file: phase w(u)=pu−q/u is a bijection (Ioi 0)→ℝ with |w'|=p+q/u²,
   so ∫₀^∞ (p+q/u²)·e^{−w(u)²} du = ∫_ℝ e^{−y²} = √π, plus integrability.
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright (pure Gaussian).
6. Manuscript: D.A2 twin / p164 rep chain. 7. Consumer: brick 1b (involution
   halving), then t=u² kernel identity, then complex extension.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real MeasureTheory Set

/-- Glasser phase `w(u) = p·u − q/u`. -/
noncomputable def glasserW (p q u : ℝ) : ℝ := p * u - q / u

/-- Glasser Gaussian factor `e^{−w(u)²}`. -/
noncomputable def glasserE (p q u : ℝ) : ℝ := Real.exp (-(glasserW p q u) ^ 2)

theorem glasserW_hasDerivAt (p q : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => glasserW p q v) (p + q / u ^ 2) u := by
  have h1 : HasDerivAt (fun v : ℝ => p * v) (p * 1) u :=
    (hasDerivAt_id u).const_mul p
  have h2 : HasDerivAt (fun v : ℝ => q * v⁻¹) (q * (-(u ^ 2)⁻¹)) u :=
    (hasDerivAt_inv (ne_of_gt hu)).const_mul q
  have h3 := h1.sub h2
  have h4 : HasDerivAt (fun v : ℝ => p * v - q * v⁻¹)
      (p * 1 - q * -(u ^ 2)⁻¹) u := by
    first
      | (refine h3.congr_of_eventuallyEq ?_
         filter_upwards with v
         simp [Pi.sub_apply])
      | simpa [Pi.sub_apply] using h3
      | exact h3
  have h5 : HasDerivAt (fun v => glasserW p q v)
      (p * 1 - q * -(u ^ 2)⁻¹) u := by
    refine h4.congr_of_eventuallyEq ?_
    filter_upwards with v
    rw [glasserW, div_eq_mul_inv]
  convert h5 using 1
  field_simp
  ring

theorem glasserW_strictMonoOn (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    StrictMonoOn (fun u => glasserW p q u) (Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  have hx0 : (0:ℝ) < x := mem_Ioi.mp hx
  have hy0 : (0:ℝ) < y := mem_Ioi.mp hy
  simp only [glasserW]
  have h1 : p * x < p * y := mul_lt_mul_of_pos_left hxy hp
  have h2 : q / y ≤ q / x := by
    first
      | gcongr
      | exact div_le_div_of_nonneg_left hq.le hx0 hxy.le
      | exact div_le_div_of_le_left hq hx0 hxy.le
  linarith

theorem glasserW_injOn (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    InjOn (fun u => glasserW p q u) (Ioi (0:ℝ)) := by
  first
    | exact (glasserW_strictMonoOn p q hp hq).injOn
    | exact StrictMonoOn.injOn (glasserW_strictMonoOn p q hp hq)

/-- The phase sweeps all of ℝ: explicit quadratic witness. -/
theorem glasserW_image (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (fun u => glasserW p q u) '' (Ioi (0:ℝ)) = univ := by
  apply Set.eq_univ_of_forall
  intro y
  set D := Real.sqrt (y ^ 2 + 4 * p * q) with hD
  have hDsq : D ^ 2 = y ^ 2 + 4 * p * q := by
    rw [hD]
    exact Real.sq_sqrt (by positivity)
  have hDgt : |y| < D := by
    rw [hD, ← Real.sqrt_sq_eq_abs]
    first
      | exact Real.sqrt_lt_sqrt (sq_nonneg y) (by nlinarith [mul_pos hp hq])
      | exact (Real.sqrt_lt_sqrt (sq_nonneg y) (by nlinarith [mul_pos hp hq]))
  have hypos : (0:ℝ) < y + D := by
    have hy1 := neg_abs_le y
    linarith
  refine ⟨(y + D) / (2 * p), mem_Ioi.mpr (by positivity), ?_⟩
  set u₀ := (y + D) / (2 * p) with hu₀
  have hu₀pos : (0:ℝ) < u₀ := by rw [hu₀]; positivity
  have hkey : p * u₀ ^ 2 = y * u₀ + q := by
    rw [hu₀]
    have h2p : (2 * p) ≠ 0 := by positivity
    field_simp
    first
      | linear_combination p * hDsq
      | linear_combination (-p) * hDsq
      | linear_combination 2 * p * hDsq
      | linear_combination hDsq
      | linear_combination (-1 : ℝ) * hDsq
      | nlinarith [hDsq]
  show glasserW p q u₀ = y
  rw [glasserW]
  have hne : u₀ ≠ 0 := ne_of_gt hu₀pos
  field_simp
  first
    | linear_combination hkey
    | linear_combination (-1 : ℝ) * hkey
    | linear_combination u₀ * hkey
    | nlinarith [hkey]

private theorem glasser_hasDerivWithin (p q : ℝ) :
    ∀ x ∈ Ioi (0:ℝ), HasDerivWithinAt (fun v => glasserW p q v)
      (p + q / x ^ 2) (Ioi (0:ℝ)) x :=
  fun x hx => (glasserW_hasDerivAt p q (mem_Ioi.mp hx)).hasDerivWithinAt

private theorem gaussian_univ_eq :
    (∫ x in (univ : Set ℝ), Real.exp (-(x ^ 2))) = Real.sqrt Real.pi := by
  have h1 : (∫ x in (univ : Set ℝ), Real.exp (-(x ^ 2)))
      = ∫ x : ℝ, Real.exp (-(x ^ 2)) := by
    first
      | exact setIntegral_univ _
      | exact MeasureTheory.setIntegral_univ _
      | simp
  rw [h1]
  have h2 : (fun x : ℝ => Real.exp (-(x ^ 2)))
      = fun x : ℝ => Real.exp (-1 * x ^ 2) := by
    funext x
    norm_num
  rw [h2, integral_gaussian]
  norm_num

/-- **Glasser substitution (brick 1a).**
`∫₀^∞ (p + q/u²)·e^{−(pu−q/u)²} du = √π`. -/
theorem glasser_substitution (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∫ u in Ioi (0:ℝ), (p + q / u ^ 2) * glasserE p q u) = Real.sqrt Real.pi := by
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (glasser_hasDerivWithin p q) (glasserW_injOn p q hp hq)
    (fun y => Real.exp (-(y ^ 2)))
  rw [glasserW_image p q hp hq, gaussian_univ_eq] at hsub
  have hcongr : (∫ u in Ioi (0:ℝ), (p + q / u ^ 2) * glasserE p q u)
      = ∫ u in Ioi (0:ℝ),
          |p + q / u ^ 2| • Real.exp (-(((fun v => glasserW p q v) u) ^ 2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : (0:ℝ) < u := mem_Ioi.mp hu
    have hpos : (0:ℝ) < p + q / u ^ 2 := by positivity
    show (p + q / u ^ 2) * glasserE p q u
        = |p + q / u ^ 2| • Real.exp (-(glasserW p q u) ^ 2)
    rw [abs_of_pos hpos, smul_eq_mul, glasserE]
  rw [hcongr]
  first
    | exact hsub.symm
    | simpa using hsub.symm
    | (rw [← hsub])

/-- **Integrability (brick 1a).** The Glasser integrand is integrable. -/
theorem glasser_sum_integrable (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun u => (p + q / u ^ 2) * glasserE p q u) (Ioi (0:ℝ)) := by
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (glasser_hasDerivWithin p q) (glasserW_injOn p q hp hq)
    (fun y => Real.exp (-(y ^ 2)))
  rw [glasserW_image p q hp hq] at hiff
  have hInt : IntegrableOn (fun y : ℝ => Real.exp (-(y ^ 2))) (univ : Set ℝ) := by
    rw [integrableOn_univ]
    have hg := integrable_exp_neg_mul_sq (b := (1:ℝ)) one_pos
    refine hg.congr ?_
    first
      | (filter_upwards with x; norm_num)
      | (apply Filter.Eventually.of_forall; intro x; norm_num)
  have h2 := hiff.mp hInt
  refine IntegrableOn.congr_fun h2 ?_ measurableSet_Ioi
  intro u hu
  have hu0 : (0:ℝ) < u := mem_Ioi.mp hu
  have hpos : (0:ℝ) < p + q / u ^ 2 := by positivity
  show |p + q / u ^ 2| • Real.exp (-(glasserW p q u) ^ 2)
      = (p + q / u ^ 2) * glasserE p q u
  rw [abs_of_pos hpos, smul_eq_mul, glasserE]

#print axioms glasserW_hasDerivAt
#print axioms glasserW_image
#print axioms glasser_substitution
#print axioms glasser_sum_integrable

end

end RHFormalization
