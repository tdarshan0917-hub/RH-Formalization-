-- SENTINEL: L0b-cos-resolvent-halfplane-v2
import RHFormalization.ResolventDenomCompactLowerBound
import RHFormalization.DA2LaplaceResolvent
import RHFormalization.CosGaussianDerivBound
import RHFormalization.CosGaussHalfLine
import RHFormalization.BSideHeatKernelLaplaceConnector
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import Mathlib

/-!
# L0b — The continuum cosine-resolvent identity on the half-plane
`cosResolvent_integral_eq_pi_kernel`:
  ∫_{Ioi 0} cos(ξa)/(s+1/4+ξ²) dξ = π · shiftedLaplaceHeatKernelC a s
for 0 ≤ a, 0 < Re s. Route: per-ξ Laplace (inv_eq_laplace_exp) → Fubini
(integrable_prod_iff certificate, majorant 4/(1+ξ²)) → inner cosGauss
half-line integral (integral_cosGauss_Ioi) → π-prefactor algebra →
banked halfplane connector. Ω-extension is L0c's job.
v2: integral_ofReal (RCLike coercion, never matches Complex.ofReal) →
integral_complex_ofReal at both crossing sites.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- The continuum cosine-resolvent integrand (per-spike continuum face). -/
def cosResolventIntegrand (a : ℝ) (s : ℂ) (ξ : ℝ) : ℂ :=
  ((Real.cos (ξ * a) : ℝ) : ℂ) / (s + (1/4 : ℂ) + (ξ : ℂ)^2)

/-- The two-variable Fubini workhorse. -/
def cosResolventF (a : ℝ) (s : ℂ) (ξ t : ℝ) : ℂ :=
  ((Real.cos (ξ * a) : ℝ) : ℂ) *
    Complex.exp (-(s + ((1/4 + ξ^2 : ℝ) : ℂ)) * (t : ℂ))

/-- Real Laplace of 1: `∫_{Ioi 0} e^{−ct} dt = 1/c`, from the banked complex
resolvent identity by ofReal-injectivity. -/
theorem real_laplace_one (c : ℝ) (hc : 0 < c) :
    (∫ t in Set.Ioi (0:ℝ), Real.exp (-c * t)) = 1 / c := by
  have hre : (0:ℝ) < ((c : ℂ)).re := by rw [Complex.ofReal_re]; exact hc
  have h := inv_eq_laplace_exp (c : ℂ) 0 le_rfl hre
  simp only [Complex.ofReal_zero, add_zero] at h
  have hcongr : (∫ t in Set.Ioi (0:ℝ), Complex.exp (-(c:ℂ) * (t:ℂ)))
      = ∫ t in Set.Ioi (0:ℝ), ((Real.exp (-c * t) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hcongr, integral_complex_ofReal, ← Complex.ofReal_inv] at h
  rw [one_div]
  exact (Complex.ofReal_inj.mp h).symm

/-- Exact norm of the workhorse integrand. -/
theorem norm_cosResolventF (a : ℝ) (s : ℂ) (ξ t : ℝ) :
    ‖cosResolventF a s ξ t‖
      = |Real.cos (ξ * a)| * Real.exp (-(s.re + (1/4 + ξ^2)) * t) := by
  unfold cosResolventF
  have hre : (-(s + ((1/4 + ξ^2 : ℝ) : ℂ)) * (t:ℂ)).re
      = -(s.re + (1/4 + ξ^2)) * t := by
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]

/-- t-marginal of the norm: exact value. -/
theorem cosResolventF_norm_integral (a : ℝ) (s : ℂ) (hs : 0 < s.re) (ξ : ℝ) :
    (∫ t in Set.Ioi (0:ℝ), ‖cosResolventF a s ξ t‖)
      = |Real.cos (ξ * a)| * (1 / (s.re + (1/4 + ξ^2))) := by
  have hδ : (0:ℝ) < s.re + (1/4 + ξ^2) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => norm_cosResolventF a s ξ t)]
  rw [integral_const_mul, real_laplace_one _ hδ]

/-- Per-ξ t-integrability. -/
theorem cosResolventF_t_integrable (a : ℝ) (s : ℂ) (hs : 0 < s.re) (ξ : ℝ) :
    Integrable (fun t => cosResolventF a s ξ t)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
  unfold cosResolventF
  apply Integrable.const_mul
  have hre : (-(s + ((1/4 + ξ^2 : ℝ) : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    nlinarith [sq_nonneg ξ]
  exact integrableOn_exp_mul_complex_Ioi hre 0

/-- **The Fubini certificate**: product integrability on `Ioi 0 × Ioi 0`. -/
theorem cosResolventF_prod_integrable (a : ℝ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (Function.uncurry (cosResolventF a s))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod
        (volume.restrict (Set.Ioi (0:ℝ)))) := by
  have hcont : Continuous (fun p : ℝ × ℝ => cosResolventF a s p.1 p.2) := by
    unfold cosResolventF
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_fst.mul continuous_const))
    · apply Complex.continuous_exp.comp
      apply Continuous.mul
      · exact (continuous_const.add (Complex.continuous_ofReal.comp
          (continuous_const.add (continuous_fst.pow 2)))).neg
      · exact Complex.continuous_ofReal.comp continuous_snd
  have h1f : AEStronglyMeasurable (Function.uncurry (cosResolventF a s))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod
        (volume.restrict (Set.Ioi (0:ℝ)))) :=
    hcont.aestronglyMeasurable
  rw [integrable_prod_iff h1f]
  constructor
  · apply Filter.Eventually.of_forall
    intro ξ
    simp only [Function.uncurry_apply_pair]
    exact cosResolventF_t_integrable a s hs ξ
  · have hrepr : (fun ξ : ℝ => ∫ t, ‖Function.uncurry (cosResolventF a s) (ξ, t)‖
        ∂(volume.restrict (Set.Ioi (0:ℝ))))
        = fun ξ : ℝ => |Real.cos (ξ * a)| * (1 / (s.re + (1/4 + ξ^2))) := by
      funext ξ
      simp only [Function.uncurry_apply_pair]
      exact cosResolventF_norm_integral a s hs ξ
    rw [hrepr]
    have hmaj : Integrable (fun ξ : ℝ => 4 * (1 + ξ^2)⁻¹)
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      (integrable_inv_one_add_sq.const_mul 4).integrableOn
    apply Integrable.mono' hmaj
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul
      · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).abs
      · apply Continuous.div continuous_const
        · exact continuous_const.add (continuous_const.add (continuous_pow 2))
        · intro ξ
          positivity
    · filter_upwards with ξ
      have hδ : (0:ℝ) < s.re + (1/4 + ξ^2) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (by positivity :
        (0:ℝ) < 1 / (s.re + (1/4 + ξ^2)))]
      have hc1 : |Real.cos (ξ * a)| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have hd : (1/4 : ℝ) * (1 + ξ^2) ≤ s.re + (1/4 + ξ^2) := by
        nlinarith [sq_nonneg ξ]
      have h2 : 1 / (s.re + (1/4 + ξ^2)) ≤ 1 / ((1/4 : ℝ) * (1 + ξ^2)) :=
        one_div_le_one_div_of_le (by positivity) hd
      have h3 : 1 / ((1/4 : ℝ) * (1 + ξ^2)) = 4 * (1 + ξ^2)⁻¹ := by
        rw [one_div, mul_inv, ← one_div]
        norm_num
      calc |Real.cos (ξ * a)| * (1 / (s.re + (1/4 + ξ^2)))
          ≤ 1 * (1 / ((1/4 : ℝ) * (1 + ξ^2))) :=
            mul_le_mul hc1 h2 (by positivity) one_pos.le
        _ = 4 * (1 + ξ^2)⁻¹ := by rw [one_mul, h3]

/-- **L0b — the continuum cosine-resolvent identity on the half-plane.** -/
theorem cosResolvent_integral_eq_pi_kernel (a : ℝ) (ha : 0 ≤ a)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ)
      = (Real.pi : ℂ) * shiftedLaplaceHeatKernelC a s := by
  have hA : ∀ ξ : ℝ, cosResolventIntegrand a s ξ
      = ∫ t in Set.Ioi (0:ℝ), cosResolventF a s ξ t := by
    intro ξ
    unfold cosResolventIntegrand
    rw [div_eq_mul_inv, denom_eq_add_real s ξ]
    rw [inv_eq_laplace_exp s (1/4 + ξ^2) (by positivity) hs]
    rw [← integral_const_mul]
    rfl
  rw [setIntegral_congr_fun measurableSet_Ioi (fun ξ _ => hA ξ)]
  rw [integral_integral_swap (cosResolventF_prod_integrable a s hs)]
  have hCD : ∀ t ∈ Set.Ioi (0:ℝ),
      (∫ ξ in Set.Ioi (0:ℝ), cosResolventF a s ξ t)
        = (Real.pi : ℂ) * shiftedHeatIntegrand a s t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have hfact : ∀ ξ : ℝ, cosResolventF a s ξ t
        = Complex.exp (-(s + (1/4 : ℂ)) * (t:ℂ)) * ((cosGauss t a ξ : ℝ) : ℂ) := by
      intro ξ
      unfold cosResolventF cosGauss
      rw [show -(s + ((1/4 + ξ^2 : ℝ) : ℂ)) * (t:ℂ)
          = -(s + (1/4 : ℂ)) * (t:ℂ) + ((-(t * ξ^2) : ℝ) : ℂ) from by
        push_cast; ring]
      rw [Complex.exp_add, ← Complex.ofReal_exp]
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun ξ _ => hfact ξ)]
    rw [integral_const_mul, integral_complex_ofReal, integral_cosGauss_Ioi t a ht0]
    have ht' : t ≠ 0 := ne_of_gt ht0
    have hsqrt_pos : (0:ℝ) < Real.sqrt (4 * Real.pi * t) :=
      Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt (Real.pi / t) * Real.sqrt (4 * Real.pi * t)
        = 2 * Real.pi := by
      rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ Real.pi / t)]
      rw [show Real.pi / t * (4 * Real.pi * t)
          = 4 * Real.pi^2 * (t / t) from by ring]
      rw [div_self ht', mul_one]
      rw [show (4:ℝ) * Real.pi^2 = (2 * Real.pi)^2 from by ring]
      exact Real.sqrt_sq (by positivity)
    have hpref : (1/2 : ℝ) * (Real.sqrt (Real.pi / t) * Real.exp (-a^2/(4*t)))
        = Real.pi * heatKernelRealScalar t a := by
      unfold heatKernelRealScalar
      rw [show Real.pi * ((1:ℝ) / Real.sqrt (4 * Real.pi * t)
          * Real.exp (-(a^2)/(4*t)))
          = Real.pi / Real.sqrt (4 * Real.pi * t)
            * Real.exp (-(a^2)/(4*t)) from by ring]
      rw [show (1/2 : ℝ) * (Real.sqrt (Real.pi / t) * Real.exp (-a^2/(4*t)))
          = (1/2 : ℝ) * Real.sqrt (Real.pi / t) * Real.exp (-a^2/(4*t)) from by
        ring]
      congr 1
      rw [eq_div_iff (ne_of_gt hsqrt_pos)]
      calc (1/2 : ℝ) * Real.sqrt (Real.pi / t) * Real.sqrt (4 * Real.pi * t)
          = (1/2 : ℝ) * (Real.sqrt (Real.pi / t)
              * Real.sqrt (4 * Real.pi * t)) := by ring
        _ = (1/2 : ℝ) * (2 * Real.pi) := by rw [hsq]
        _ = Real.pi := by ring
    rw [hpref]
    unfold shiftedHeatIntegrand
    rw [heatKernelG_eq_realScalar, Complex.ofReal_mul]
    rw [show -(s + (1/4 : ℂ)) * (t:ℂ) = -s * (t:ℂ) + (-(t:ℂ)/4) from by ring]
    rw [Complex.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hCD t ht)]
  rw [integral_const_mul]
  rw [← shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane a ha s hs]

#print axioms real_laplace_one
#print axioms norm_cosResolventF
#print axioms cosResolventF_norm_integral
#print axioms cosResolventF_prod_integrable
#print axioms cosResolvent_integral_eq_pi_kernel

end

end RHFormalization
