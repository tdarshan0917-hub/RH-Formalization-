import RHFormalization.HeatKernelLaplaceBase
import Mathlib

/-!
# Keystone Glasser integral (the a>0 hard kernel).

  INT_0^inf e^{-b u^2 - c^2/u^2} du = (sqrt pi / (2 sqrt b)) e^{-2 c sqrt b}   (b,c > 0)

Strategy (classical, self-reciprocal): complete the square
  b u^2 + c^2/u^2 = (sqrt b u - c/u)^2 + 2 c sqrt b,
then the self-map u -> c/(sqrt b u) shows ∫ e^{-(sqrt b u - c/u)^2} du = ∫ e^{-b u^2} du,
which is the half-line Gaussian = sqrt(pi/b)/2. The e^{-2 c sqrt b} factors out.

STATUS: target stated. Completing-the-square algebra below (tractable);
the self-map invariance is the remaining hard analytic step.
-/

namespace RHFormalization
open Real MeasureTheory Set
open scoped BigOperators

/-- Completing the square: for u > 0, b,c > 0,
b u^2 + c^2/u^2 = (sqrt b * u - c/u)^2 + 2 c sqrt b. -/
theorem glasser_complete_square (b c u : Real) (hb : 0 < b) (hu : 0 < u) :
    b * u^2 + c^2 / u^2 = (Real.sqrt b * u - c/u)^2 + 2 * c * Real.sqrt b := by
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hu2 : u^2 > 0 := by positivity
  field_simp
  ring_nf
  rw [hsb]
  ring

/-- The map phi(u) = sqrt b * u - c/u, the Glasser substitution. -/
noncomputable def glasserPhi (b c : Real) (u : Real) : Real :=
  Real.sqrt b * u - c / u

/-- **Derivative of glasserPhi**: phi'(u) = sqrt b + c/u^2 for u > 0. -/
theorem hasDerivAt_glasserPhi (b c u : Real) (hu : u ≠ 0) :
    HasDerivAt (glasserPhi b c) (Real.sqrt b + c / u^2) u := by
  unfold glasserPhi
  have h1 : HasDerivAt (fun x : Real => Real.sqrt b * x) (Real.sqrt b) u := by
    simpa using (hasDerivAt_id u).const_mul (Real.sqrt b)
  have h2 : HasDerivAt (fun x : Real => c / x) (-(c / u^2)) u := by
    have hinv : HasDerivAt (fun x : Real => x⁻¹) (-(u^2)⁻¹) u := hasDerivAt_inv hu
    have hcm := hinv.const_mul c
    -- hcm : HasDerivAt (fun x => c * x⁻¹) (c * -(u^2)⁻¹) u
    have heq1 : (fun x : Real => c * x⁻¹) = (fun x : Real => c / x) := by
      funext x; rw [div_eq_mul_inv]
    have heq2 : c * -(u^2)⁻¹ = -(c / u^2) := by
      rw [div_eq_mul_inv]; ring
    rw [heq1, heq2] at hcm
    exact hcm
  have hsub := h1.sub h2
  convert hsub using 1
  ring

/-- The reciprocal self-map v = c/(sqrt b * u). -/
noncomputable def glasserRecip (b c : Real) (u : Real) : Real :=
  c / (Real.sqrt b * u)

/-- **Reciprocal symmetry**: phi(c/(sqrt b * u)) = -phi(u) for b,c,u > 0. -/
theorem glasserPhi_recip (b c u : Real) (hb : 0 < b) (hc : 0 < c) (hu : 0 < u) :
    glasserPhi b c (glasserRecip b c u) = - glasserPhi b c u := by
  unfold glasserPhi glasserRecip
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsb2 : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have hbu : Real.sqrt b * u ≠ 0 := by positivity
  rw [eq_neg_iff_add_eq_zero]
  field_simp
  nlinarith [hsb2, Real.sqrt_nonneg b]

/-- Integrability of u -> exp(-(glasserPhi b c u)^2) on Ioi 0, via comparison
with the Gaussian exp(-b u^2): phi(u)^2 >= b u^2 - 2 c sqrt b. -/
theorem integrableOn_exp_neg_glasserPhi_sq (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun u : Real => Real.exp (-(glasserPhi b c u)^2)) (Set.Ioi 0) := by
  have hgauss : IntegrableOn (fun u : Real => Real.exp (-b * u^2)) (Set.Ioi 0) :=
    (integrableOn_Ioi_exp_neg_mul_sq_iff).mpr hb
  -- bound: exp(-(phi)^2) <= exp(2 c sqrt b) * exp(-b u^2) on Ioi 0
  apply Integrable.mono' (g := fun u : Real => Real.exp (2 * c * Real.sqrt b) * Real.exp (-b * u^2))
  · exact hgauss.const_mul _
  · apply (Measurable.exp ?_).aestronglyMeasurable
    apply Measurable.neg
    exact ((measurable_const.mul measurable_id).sub (measurable_const.div measurable_id)).pow measurable_const
  · have hmeas : MeasurableSet (Set.Ioi (0:Real)) := measurableSet_Ioi
    filter_upwards [ae_restrict_mem hmeas] with u hu
    have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcs : b * u^2 + c^2 / u^2 = (glasserPhi b c u)^2 + 2 * c * Real.sqrt b := by
      unfold glasserPhi; rw [glasser_complete_square b c u hb hu0]
    have hpos : c^2 / u^2 ≥ 0 := by positivity
    nlinarith [hpos, hcs]
  
/-- Derivative of the reciprocal self-map rho(u) = c/(sqrt b * u): rho'(u) = -c/(sqrt b * u^2). -/
theorem hasDerivAt_glasserRecip (b c u : Real) (hb : 0 < b) (hu : 0 < u) :
    HasDerivWithinAt (glasserRecip b c) (-(c / (Real.sqrt b * u^2))) (Set.Ioi 0) u := by
  unfold glasserRecip
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hbu : Real.sqrt b * u ≠ 0 := by positivity
  -- c/(sqrt b * u) = (c/sqrt b) * u⁻¹
  have hrw : (fun u : Real => c / (Real.sqrt b * u)) = (fun u : Real => (c / Real.sqrt b) * u⁻¹) := by
    funext x; rw [div_mul_eq_div_div, div_eq_mul_inv]
  rw [hrw]
  have hinv : HasDerivAt (fun x : Real => x⁻¹) (-(u^2)⁻¹) u := hasDerivAt_inv hu.ne'
  have hcm := (hinv.const_mul (c / Real.sqrt b)).hasDerivWithinAt (s := Set.Ioi 0)
  convert hcm using 1
  field_simp

/-- The reciprocal self-map is injective on Ioi 0. -/
theorem injOn_glasserRecip (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    Set.InjOn (glasserRecip b c) (Set.Ioi 0) := by
  unfold glasserRecip
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hbx : Real.sqrt b * x ≠ 0 := by positivity
  have hby : Real.sqrt b * y ≠ 0 := by positivity
  field_simp at hxy
  -- from c * (sqrt b * y) = c * (sqrt b * x) get x = y
  have hc0 : c ≠ 0 := hc.ne'
  nlinarith [hxy, hsb, hx0, hy0, hc]

/-- The reciprocal self-map maps Ioi 0 onto Ioi 0. -/
theorem image_glasserRecip (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    (glasserRecip b c) '' (Set.Ioi 0) = Set.Ioi 0 := by
  unfold glasserRecip
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  ext x
  rw [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : 0 < y := hy
    simp only [Set.mem_Ioi]
    positivity
  · intro hx
    have hx0 : 0 < x := hx
    refine ⟨c / (Real.sqrt b * x), ?_, ?_⟩
    · simp only [Set.mem_Ioi]; positivity
    · field_simp

/-- **Build 2: weighted reciprocal identity.**
INT_{Ioi 0} e^{-phi^2} * (c/u^2) du = sqrt b * INT_{Ioi 0} e^{-phi^2} du.
Proved by the change-of-variables u -> rho(u) = c/(sqrt b u), using phi(rho u) = -phi u. -/
theorem glasser_weighted_reciprocal (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    (∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2) * (c / u^2))
      = Real.sqrt b * ∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  -- change of variables: ∫_{rho '' Ioi 0} g = ∫_{Ioi 0} |rho'| • g(rho)
  have hcov := integral_image_eq_integral_abs_deriv_smul (F := Real)
    (measurableSet_Ioi)
    (f := glasserRecip b c)
    (f' := fun u => -(c / (Real.sqrt b * u^2)))
    (s := Set.Ioi 0)
    (fun u hu => hasDerivAt_glasserRecip b c u hb hu)
    (injOn_glasserRecip b c hb hc)
    (fun v => Real.exp (-(glasserPhi b c v)^2))
  rw [image_glasserRecip b c hb hc] at hcov
  -- hcov : ∫_{Ioi 0} e^{-phi^2} = ∫_{Ioi 0} |rho'(u)| • e^{-phi(rho u)^2}
  -- simplify RHS: phi(rho u) = -phi u, so e^{-phi(rho u)^2} = e^{-phi u ^2}; |rho'| = c/(sqrt b u^2)
  have hrhs : (∫ u in Set.Ioi (0:Real),
        |(-(c / (Real.sqrt b * u^2)))| • Real.exp (-(glasserPhi b c (glasserRecip b c u))^2))
      = ∫ u in Set.Ioi (0:Real), (c / (Real.sqrt b * u^2)) * Real.exp (-(glasserPhi b c u)^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := hu
    simp only []
    rw [glasserPhi_recip b c u hb hc hu0, neg_sq, smul_eq_mul]
    congr 1
    rw [abs_neg, abs_of_nonneg (by positivity)]
  rw [hrhs] at hcov
  -- hcov : ∫ e^{-phi^2} = ∫ (c/(sqrt b u^2)) e^{-phi^2}
  -- pull out 1/sqrt b : ∫ (c/(sqrt b u^2)) e^{-phi^2} = (1/sqrt b) ∫ (c/u^2) e^{-phi^2}
  have hfactor : (∫ u in Set.Ioi (0:Real), (c / (Real.sqrt b * u^2)) * Real.exp (-(glasserPhi b c u)^2))
      = (1 / Real.sqrt b) * ∫ u in Set.Ioi (0:Real), (c / u^2) * Real.exp (-(glasserPhi b c u)^2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp only []
    rw [← mul_assoc]
    congr 1
    field_simp
  rw [hfactor] at hcov
  -- hcov : ∫ e^{-phi^2} = (1/sqrt b) ∫ (c/u^2) e^{-phi^2}
  -- so ∫ (c/u^2) e^{-phi^2} = sqrt b ∫ e^{-phi^2}
  have hgoal : (∫ u in Set.Ioi (0:Real), (c / u^2) * Real.exp (-(glasserPhi b c u)^2))
      = Real.sqrt b * ∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2) := by
    rw [hcov]
    field_simp
  -- rewrite goal's integrand order (e^{-phi^2} * (c/u^2)) = ((c/u^2) * e^{-phi^2})
  rw [show (∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2) * (c / u^2))
      = ∫ u in Set.Ioi (0:Real), (c / u^2) * Real.exp (-(glasserPhi b c u)^2) from by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu; ring]
  exact hgoal

/-- glasserPhi is strictly monotone on Ioi 0 (since sqrt b * u increases and -c/u increases). -/
theorem strictMonoOn_glasserPhi (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    StrictMonoOn (glasserPhi b c) (Set.Ioi 0) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  unfold glasserPhi
  -- sqrt b * x - c/x < sqrt b * y - c/y
  have ht1 : Real.sqrt b * x < Real.sqrt b * y := by
    apply mul_lt_mul_of_pos_left hxy hsb
  have ht2 : c / y < c / x := by
    apply div_lt_div_of_pos_left hc hx0 hxy
  linarith

/-- glasserPhi is injective on Ioi 0. -/
theorem injOn_glasserPhi (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    Set.InjOn (glasserPhi b c) (Set.Ioi 0) :=
  (strictMonoOn_glasserPhi b c hb hc).injOn

/-- glasserPhi is continuous on Ioi 0. -/
theorem continuousOn_glasserPhi (b c : Real) :
    ContinuousOn (glasserPhi b c) (Set.Ioi 0) := by
  unfold glasserPhi
  apply ContinuousOn.sub
  · exact (continuous_const.mul continuous_id).continuousOn
  · apply ContinuousOn.div continuousOn_const continuousOn_id
    intro u hu
    exact (ne_of_gt hu)

/-- glasserPhi tends to atTop as u -> atTop (sqrt b * u dominates). -/
theorem tendsto_glasserPhi_atTop (b c : Real) (hb : 0 < b) :
    Filter.Tendsto (glasserPhi b c) Filter.atTop Filter.atTop := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  unfold glasserPhi
  have h1 : Filter.Tendsto (fun u : Real => Real.sqrt b * u) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hsb Filter.tendsto_id
  have h2 : Filter.Tendsto (fun u : Real => c / u) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  -- sqrt b * u - c/u = sqrt b * u + (- c/u), atTop + (tendsto to 0)
  have h3 : Filter.Tendsto (fun u : Real => Real.sqrt b * u + (- (c / u))) Filter.atTop Filter.atTop :=
    h1.atTop_add (h2.neg)
  have heq : (fun u : Real => Real.sqrt b * u - c / u) = (fun u : Real => Real.sqrt b * u + (- (c / u))) := by
    funext u; ring
  rw [heq]; exact h3

/-- glasserPhi tends to atBot as u -> 0+ (-c/u dominates). -/
theorem tendsto_glasserPhi_nhdsGT_zero (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    Filter.Tendsto (glasserPhi b c) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  unfold glasserPhi
  -- prove -(phi) -> atTop, then negate
  rw [← Filter.tendsto_neg_atTop_iff]
  -- goal: Tendsto (fun u => -(sqrt b * u - c/u)) (nhdsWithin ..) atTop
  -- -(sqrt b * u - c/u) = c/u - sqrt b * u = c/u + (-(sqrt b * u))
  have hinv : Filter.Tendsto (fun u : Real => u⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have hcdiv : Filter.Tendsto (fun u : Real => c / u) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    have hee : (fun u : Real => c / u) = (fun u : Real => c * u⁻¹) := by funext u; rw [div_eq_mul_inv]
    rw [hee]
    exact Filter.Tendsto.const_mul_atTop hc hinv
  have hlin : Filter.Tendsto (fun u : Real => -(Real.sqrt b * u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc0 : Filter.Tendsto (fun u : Real => -(Real.sqrt b * u)) (nhds 0) (nhds (-(Real.sqrt b * 0))) :=
      ((continuous_const.mul continuous_id).neg).tendsto 0
    rw [mul_zero, neg_zero] at hc0
    exact hc0.mono_left nhdsWithin_le_nhds
  have h3 : Filter.Tendsto (fun u : Real => c/u + (-(Real.sqrt b * u))) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    hcdiv.atTop_add hlin
  have heq : (fun u : Real => -(Real.sqrt b * u - c / u)) = (fun u : Real => c/u + (-(Real.sqrt b * u))) := by
    funext u; ring
  rw [heq]; exact h3

/-- The image of glasserPhi over Ioi 0 is all of R (surjectivity via IVT + the two limits). -/
theorem image_glasserPhi_eq_univ (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    (glasserPhi b c) '' (Set.Ioi 0) = Set.univ := by
  have hsurj : Set.SurjOn (glasserPhi b c) (Set.Ioi 0) Set.univ := by
    apply ContinuousOn.surjOn_of_tendsto (Set.nonempty_Ioi) (continuousOn_glasserPhi b c)
    · -- Tendsto (fun x : Ioi 0 => phi x) atBot atBot
      rw [tendsto_comp_coe_Ioi_atBot]
      exact tendsto_glasserPhi_nhdsGT_zero b c hb hc
    · -- Tendsto (fun x : Ioi 0 => phi x) atTop atTop
      have hcoe : Filter.Tendsto (fun x : Set.Ioi (0:Real) => (x : Real)) Filter.atTop Filter.atTop := by
        rw [Filter.atTop_Ioi_eq]
        exact Filter.tendsto_comap
      exact (tendsto_glasserPhi_atTop b c hb).comp hcoe
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro y _
  exact hsurj (Set.mem_univ y)

/-- **Build 3: full-line Gaussian substitution.**
INT_{Ioi 0} e^{-phi^2} * (sqrt b + c/u^2) du = INT_R e^{-w^2} dw = sqrt pi.
Via the change-of-variables w = phi(u), whose image over Ioi 0 is all of R. -/
theorem glasser_full_gaussian (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    (∫ u in Set.Ioi (0:Real),
        Real.exp (-(glasserPhi b c u)^2) * (Real.sqrt b + c / u^2))
      = Real.sqrt Real.pi := by
  -- change of variables via the image map phi
  have hcov := integral_image_eq_integral_abs_deriv_smul (F := Real)
    (measurableSet_Ioi)
    (f := glasserPhi b c)
    (f' := fun u => Real.sqrt b + c / u^2)
    (s := Set.Ioi 0)
    (fun u hu => (hasDerivAt_glasserPhi b c u (ne_of_gt hu)).hasDerivWithinAt)
    (injOn_glasserPhi b c hb hc)
    (fun w => Real.exp (-w^2))
  rw [image_glasserPhi_eq_univ b c hb hc] at hcov
  -- hcov : INT_{univ} e^{-w^2} = INT_{Ioi 0} |phi'| • e^{-phi(u)^2}
  rw [Measure.restrict_univ] at hcov
  -- LHS of hcov : ∫ (w : R) e^{-w^2} = sqrt pi
  have hgauss : (∫ w : Real, Real.exp (-w^2)) = Real.sqrt Real.pi := by
    have := integral_gaussian 1
    rw [show (fun x : Real => Real.exp (-1 * x^2)) = (fun x : Real => Real.exp (-x^2)) from by
      funext x; ring_nf] at this
    rw [this]; rw [div_one]
  rw [hgauss] at hcov
  -- hcov : sqrt pi = INT_{Ioi 0} |sqrt b + c/u^2| • e^{-phi^2}
  -- rewrite goal integrand into the |.|• form, then close with hcov.symm
  have heq : (∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2) * (Real.sqrt b + c / u^2))
        = ∫ u in Set.Ioi (0:Real), |Real.sqrt b + c / u^2| • Real.exp (-(glasserPhi b c u)^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := hu
    simp only []
    rw [smul_eq_mul, abs_of_nonneg (by positivity : (0:Real) ≤ Real.sqrt b + c / u^2)]
    ring
  rw [heq]
  exact hcov.symm

/-- Integrability of the full Build-3 integrand e^{-phi^2}*(sqrt b + c/u^2) on Ioi 0,
via the change-of-variables image of the integrable gaussian. -/
theorem integrableOn_exp_glasserPhi_full (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun u : Real => Real.exp (-(glasserPhi b c u)^2) * (Real.sqrt b + c / u^2)) (Set.Ioi 0) := by
  -- via integrableOn_image_iff_integrableOn_abs_deriv_smul: integrable on image (univ) <-> integrable |phi'|•g(phi)
  have hg : IntegrableOn (fun w : Real => Real.exp (-w^2)) Set.univ := by
    rw [integrableOn_univ]
    have := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
    simpa [one_mul] using this
  have himg := integrableOn_image_iff_integrableOn_abs_deriv_smul (F := Real)
    (measurableSet_Ioi)
    (f := glasserPhi b c)
    (f' := fun u => Real.sqrt b + c / u^2)
    (s := Set.Ioi 0)
    (fun u hu => (hasDerivAt_glasserPhi b c u (ne_of_gt hu)).hasDerivWithinAt)
    (injOn_glasserPhi b c hb hc)
    (fun w => Real.exp (-w^2))
  rw [image_glasserPhi_eq_univ b c hb hc] at himg
  rw [himg] at hg
  -- hg : IntegrableOn (fun u => |sqrt b + c/u^2| • e^{-phi^2}) (Ioi 0)
  apply hg.congr_fun _ measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := hu
  simp only []
  rw [smul_eq_mul, abs_of_nonneg (by positivity : (0:Real) ≤ Real.sqrt b + c / u^2)]
  ring

/-- Integrability of u -> e^{-phi^2} * (c/u^2) on Ioi 0 (difference of full integrand and sqrt b * e^{-phi^2}). -/
theorem integrableOn_exp_glasserPhi_weight (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun u : Real => Real.exp (-(glasserPhi b c u)^2) * (c / u^2)) (Set.Ioi 0) := by
  have hfull := integrableOn_exp_glasserPhi_full b c hb hc
  have hpart := (integrableOn_exp_neg_glasserPhi_sq b c hb hc).const_mul (Real.sqrt b)
  have hdiff := hfull.sub hpart
  apply hdiff.congr_fun _ measurableSet_Ioi
  intro u hu
  simp only [Pi.sub_apply]
  ring_nf

/-- INT_{Ioi 0} e^{-phi^2} du = sqrt pi / (2 sqrt b). Combines Build 2 and Build 3. -/
theorem glasser_phi_integral (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    (∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2))
      = Real.sqrt Real.pi / (2 * Real.sqrt b) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hfull := glasser_full_gaussian b c hb hc
  have hweighted := glasser_weighted_reciprocal b c hb hc
  -- split the full integrand: e^{-phi^2}(sqrt b + c/u^2) = sqrt b * e^{-phi^2} + e^{-phi^2}(c/u^2)
  have hsplit : (∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2) * (Real.sqrt b + c / u^2))
      = (∫ u in Set.Ioi (0:Real), Real.sqrt b * Real.exp (-(glasserPhi b c u)^2))
        + ∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2) * (c / u^2) := by
    rw [← MeasureTheory.integral_add]
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      ring
    · exact (integrableOn_exp_neg_glasserPhi_sq b c hb hc).const_mul _
    · exact integrableOn_exp_glasserPhi_weight b c hb hc
  rw [hsplit, hweighted, integral_const_mul] at hfull
  -- hfull : sqrt b * I + sqrt b * I = sqrt pi  where I = INT e^{-phi^2}
  -- so 2 sqrt b * I = sqrt pi
  have h2 : 2 * Real.sqrt b * (∫ u in Set.Ioi (0:Real), Real.exp (-(glasserPhi b c u)^2)) = Real.sqrt Real.pi := by
    rw [← hfull]; ring
  field_simp at h2 ⊢
  linarith [h2]

/-- **Build 4: the Glasser integral.**
INT_{Ioi 0} e^{-(b u^2 + c^2/u^2)} du = sqrt pi / (2 sqrt b) * e^{-2 c sqrt b}, for b,c > 0. -/
theorem glasser_integral (b c : Real) (hb : 0 < b) (hc : 0 < c) :
    (∫ u in Set.Ioi (0:Real), Real.exp (-(b * u^2 + c^2 / u^2)))
      = Real.sqrt Real.pi / (2 * Real.sqrt b) * Real.exp (-(2 * c * Real.sqrt b)) := by
  -- e^{-(b u^2 + c^2/u^2)} = e^{-2 c sqrt b} * e^{-phi^2}  (by complete square)
  have hrw : (∫ u in Set.Ioi (0:Real), Real.exp (-(b * u^2 + c^2 / u^2)))
      = ∫ u in Set.Ioi (0:Real), Real.exp (-(2 * c * Real.sqrt b)) * Real.exp (-(glasserPhi b c u)^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := hu
    simp only []
    rw [← Real.exp_add]
    congr 1
    rw [glasser_complete_square b c u hb hu0]
    unfold glasserPhi
    ring
  rw [hrw, integral_const_mul, glasser_phi_integral b c hb hc]
  ring

end RHFormalization
