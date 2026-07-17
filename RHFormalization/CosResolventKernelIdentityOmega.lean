-- SENTINEL: L0c-cos-resolvent-omega-v1
import RHFormalization.CosResolventKernelIdentityHalfplane
import RHFormalization.AdaptiveDefectHolo
import RHFormalization.OmegaConnected
import RHFormalization.SphereUniformConvergence
import Mathlib

/-!
# L0c — The continuum cosine-resolvent identity on all of Ω
`cosResolvent_integral_eq_pi_kernel_Omega`:
  ∫_{Ioi 0} cos(ξa)/(s+1/4+ξ²) dξ = π · shiftedLaplaceHeatKernelC a s, s ∈ Ω.
Route: LHS differentiable on Ω by dominated derivative (majorants from the
L0a floor on a closed ball); both sides AnalyticOnNhd on Ω; identity theorem
(eqOn_of_preconnected_of_eventuallyEq over isPreconnected_Omega_native)
anchored at s = 1 with the banked L0b half-plane identity. Completes the
pre-L1 toolkit: L1 (per-spike Riemann-sum estimate) opens next.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory Metric

/-- The continuum side as a function of `s`. -/
def cosResolventLHS (a : ℝ) (s : ℂ) : ℂ :=
  ∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ

/-- Pointwise s-derivative of the integrand where the denominator is nonzero. -/
theorem cosResolventIntegrand_hasDerivAt (a : ℝ) (ξ : ℝ) {z : ℂ}
    (hz : z + (1/4 : ℂ) + (ξ : ℂ)^2 ≠ 0) :
    HasDerivAt (fun w => cosResolventIntegrand a w ξ)
      (-((Real.cos (ξ * a) : ℝ) : ℂ) / (z + (1/4 : ℂ) + (ξ : ℂ)^2)^2) z := by
  have h1 : HasDerivAt (fun w : ℂ => w + (1/4 : ℂ) + (ξ : ℂ)^2) 1 z :=
    ((hasDerivAt_id z).add_const _).add_const _
  have h2 : HasDerivAt (fun w : ℂ => (w + (1/4 : ℂ) + (ξ : ℂ)^2)⁻¹)
      (-1 / (z + (1/4 : ℂ) + (ξ : ℂ)^2)^2) z := h1.inv hz
  have h3 := h2.const_mul ((Real.cos (ξ * a) : ℝ) : ℂ)
  have hfun : (fun w : ℂ => cosResolventIntegrand a w ξ)
      = fun w : ℂ => ((Real.cos (ξ * a) : ℝ) : ℂ) * (w + (1/4 : ℂ) + (ξ : ℂ)^2)⁻¹ := by
    funext w
    unfold cosResolventIntegrand
    rw [div_eq_mul_inv]
  rw [hfun]
  convert h3 using 1
  ring

/-- Measurability of the integrand in ξ (every `z`). -/
theorem cosResolventIntegrand_aesm (a : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun ξ : ℝ => cosResolventIntegrand a z ξ)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
  apply Measurable.aestronglyMeasurable
  unfold cosResolventIntegrand
  apply Measurable.div
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))).measurable
  · exact (continuous_const.add (Complex.continuous_ofReal.pow 2)).measurable

/-- Measurability of the derivative integrand in ξ. -/
theorem cosResolventDeriv_aesm (a : ℝ) (z : ℂ) :
    AEStronglyMeasurable
      (fun ξ : ℝ => -((Real.cos (ξ * a) : ℝ) : ℂ) / (z + (1/4 : ℂ) + (ξ : ℂ)^2)^2)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
  apply Measurable.aestronglyMeasurable
  apply Measurable.div
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))).neg.measurable
  · exact ((continuous_const.add (Complex.continuous_ofReal.pow 2)).pow 2).measurable

/-- **LHS Ω-differentiability** via dominated derivative + the L0a floor. -/
theorem cosResolventLHS_differentiableAt_Omega (a : ℝ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    DifferentiableAt ℂ (cosResolventLHS a) z₀ := by
  obtain ⟨ε, hε, hballΩ⟩ := Metric.isOpen_iff.mp isOpen_Omega_proved z₀ hz₀
  have hr : (0:ℝ) < ε/2 := by linarith
  have hKΩ : closedBall z₀ (ε/2) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hballΩ
  obtain ⟨c, hc, hfloor⟩ := resolventDenom_lower_bound (closedBall z₀ (ε/2))
    (isCompact_closedBall z₀ (ε/2)) hKΩ
  have hz₀K : z₀ ∈ closedBall z₀ (ε/2) := Metric.mem_closedBall_self hr.le
  have hUnhds : Metric.ball z₀ (ε/2) ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hr
  have hcos1 : ∀ ξ : ℝ, |Real.cos (ξ * a)| ≤ 1 := fun ξ =>
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  -- F-integrability at z₀
  have hint0 : IntegrableOn (fun ξ : ℝ => cosResolventIntegrand a z₀ ξ)
      (Set.Ioi (0:ℝ)) volume := by
    have hmaj : Integrable (fun ξ : ℝ => (1/c) * (1 + ξ^2)⁻¹)
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      (integrable_inv_one_add_sq.const_mul (1/c)).integrableOn
    refine hmaj.mono' (cosResolventIntegrand_aesm a z₀) ?_
    filter_upwards with ξ
    have hfl := hfloor z₀ hz₀K ξ
    have hpos : (0:ℝ) < c * (1 + ξ^2) := by positivity
    unfold cosResolventIntegrand
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc |Real.cos (ξ * a)| / ‖z₀ + (1/4 : ℂ) + (ξ : ℂ)^2‖
        = |Real.cos (ξ * a)| * (1 / ‖z₀ + (1/4 : ℂ) + (ξ : ℂ)^2‖) := by
          rw [mul_one_div]
      _ ≤ 1 * (1 / (c * (1 + ξ^2))) :=
          mul_le_mul (hcos1 ξ) (one_div_le_one_div_of_le hpos hfl)
            (by positivity) one_pos.le
      _ = (1/c) * (1 + ξ^2)⁻¹ := by
          rw [one_mul, one_div, mul_inv, one_div]
  -- derivative bound on the ball
  have hbound : ∀ᵐ (ξ : ℝ) ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ∀ z ∈ Metric.ball z₀ (ε/2),
        ‖-((Real.cos (ξ * a) : ℝ) : ℂ) / (z + (1/4 : ℂ) + (ξ : ℂ)^2)^2‖
          ≤ (1/c^2) * (1 + ξ^2)⁻¹ := by
    filter_upwards with ξ
    intro z hz
    have hzK : z ∈ closedBall z₀ (ε/2) := Metric.ball_subset_closedBall hz
    have hfl := hfloor z hzK ξ
    have hpos : (0:ℝ) < c * (1 + ξ^2) := by positivity
    have hsq : (c * (1 + ξ^2))^2 ≤ ‖z + (1/4 : ℂ) + (ξ : ℂ)^2‖^2 := by
      nlinarith [hfl, hpos, norm_nonneg (z + (1/4 : ℂ) + (ξ : ℂ)^2)]
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    calc |Real.cos (ξ * a)| / ‖z + (1/4 : ℂ) + (ξ : ℂ)^2‖^2
        = |Real.cos (ξ * a)| * (1 / ‖z + (1/4 : ℂ) + (ξ : ℂ)^2‖^2) := by
          rw [mul_one_div]
      _ ≤ 1 * (1 / (c * (1 + ξ^2))^2) :=
          mul_le_mul (hcos1 ξ) (one_div_le_one_div_of_le (by positivity) hsq)
            (by positivity) one_pos.le
      _ ≤ (1/c^2) * (1 + ξ^2)⁻¹ := by
          rw [one_mul]
          have hsplit : (1:ℝ) / (c * (1 + ξ^2))^2
              = (1/c^2) * (1 / (1 + ξ^2)^2) := by
            rw [mul_pow]
            rw [one_div, mul_inv, one_div, one_div]
          rw [hsplit]
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hA : (1 + ξ^2) ≤ (1 + ξ^2)^2 := by nlinarith [sq_nonneg ξ]
          have hB : (1:ℝ) / (1 + ξ^2)^2 ≤ 1 / (1 + ξ^2) :=
            one_div_le_one_div_of_le (by positivity) hA
          rw [← one_div]
          exact hB
  have hbound_int : IntegrableOn (fun ξ : ℝ => (1/c^2) * (1 + ξ^2)⁻¹)
      (Set.Ioi (0:ℝ)) volume :=
    (integrable_inv_one_add_sq.const_mul (1/c^2)).integrableOn
  have hderiv : ∀ᵐ (ξ : ℝ) ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ∀ z ∈ Metric.ball z₀ (ε/2),
        HasDerivAt (fun w : ℂ => cosResolventIntegrand a w ξ)
          (-((Real.cos (ξ * a) : ℝ) : ℂ) / (z + (1/4 : ℂ) + (ξ : ℂ)^2)^2) z := by
    filter_upwards with ξ
    intro z hz
    have hzΩ : z ∈ Ω := hKΩ (Metric.ball_subset_closedBall hz)
    exact cosResolventIntegrand_hasDerivAt a ξ (denom_ne_zero_of_mem_Omega hzΩ ξ)
  have hmeas : ∀ᶠ (z : ℂ) in nhds z₀,
      AEStronglyMeasurable (fun ξ : ℝ => cosResolventIntegrand a z ξ)
        (volume.restrict (Set.Ioi (0:ℝ))) :=
    Filter.Eventually.of_forall (fun z => cosResolventIntegrand_aesm a z)
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ξ : ℝ => (1/c^2) * (1 + ξ^2)⁻¹)
    (F := fun z ξ => cosResolventIntegrand a z ξ)
    (F' := fun z ξ =>
      -((Real.cos (ξ * a) : ℝ) : ℂ) / (z + (1/4 : ℂ) + (ξ : ℂ)^2)^2)
    hUnhds hmeas hint0 (cosResolventDeriv_aesm a z₀) hbound hbound_int hderiv
  exact result.2.differentiableAt

/-- LHS analytic on Ω. -/
theorem cosResolventLHS_analytic_Omega (a : ℝ) :
    AnalyticOnNhd ℂ (cosResolventLHS a) Ω := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (cosResolventLHS_differentiableAt_Omega a hz).differentiableWithinAt
  · exact isOpen_Omega_proved

/-- RHS analytic on Ω (banked per-atom holomorphy times a constant). -/
theorem cosResolventRHS_analytic_Omega (a : ℝ) :
    AnalyticOnNhd ℂ (fun s : ℂ => (Real.pi : ℂ) * shiftedLaplaceHeatKernelC a s) Ω := by
  intro z hz
  exact analyticAt_const.mul (shiftedLaplaceHeatKernelC_holomorphicAt_Omega a hz)

/-- The anchor point lies in Ω. -/
theorem one_mem_Omega : (1:ℂ) ∈ Ω := by
  intro hax
  obtain ⟨him, hre⟩ := hax
  rw [Complex.one_re] at hre
  linarith

/-- **L0c — the identity on all of Ω** (identity theorem over the banked
half-plane identity). -/
theorem cosResolvent_eqOn_Omega (a : ℝ) (ha : 0 ≤ a) :
    Set.EqOn (cosResolventLHS a)
      (fun s : ℂ => (Real.pi : ℂ) * shiftedLaplaceHeatKernelC a s) Ω := by
  apply (cosResolventLHS_analytic_Omega a).eqOn_of_preconnected_of_eventuallyEq
    (cosResolventRHS_analytic_Omega a) isPreconnected_Omega_native one_mem_Omega
  have hmem : {s : ℂ | 0 < s.re} ∈ nhds (1:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  filter_upwards [hmem] with z hz
  exact cosResolvent_integral_eq_pi_kernel a ha z hz

/-- Unfolded form: the raw integral identity on Ω. -/
theorem cosResolvent_integral_eq_pi_kernel_Omega (a : ℝ) (ha : 0 ≤ a)
    {s : ℂ} (hs : s ∈ Ω) :
    (∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ)
      = (Real.pi : ℂ) * shiftedLaplaceHeatKernelC a s :=
  cosResolvent_eqOn_Omega a ha hs

#print axioms cosResolventIntegrand_hasDerivAt
#print axioms cosResolventLHS_differentiableAt_Omega
#print axioms cosResolventLHS_analytic_Omega
#print axioms one_mem_Omega
#print axioms cosResolvent_eqOn_Omega
#print axioms cosResolvent_integral_eq_pi_kernel_Omega

end

end RHFormalization
