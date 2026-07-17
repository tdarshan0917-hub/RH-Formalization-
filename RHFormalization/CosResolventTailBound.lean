-- SENTINEL: L1c-cos-resolvent-tail-v2
import RHFormalization.CosResolventDerivMajorant
import Mathlib

/-!
# L1c — Continuum truncation tail for the cosine-resolvent integral
1. `integral_Ioi_inv_sq`: ∫_{Ioi M} ξ⁻² = M⁻¹.
2. `cosResolventIntegrand_integrableOn_Ioi`: Ω-integrability certificate.
3. `cosResolvent_interval_vs_Ioi`: ‖∫₀^M f − ∫_{Ioi 0} f‖ ≤ 1/(c·M).
v2: hasDerivAt_inv direct (id⁻¹ Pi-atom trap); rpow literal (-2) normalized
via show before rpow_neg (literal -2 ≠ syntactic -(2)); field_simp closes
the c⁻¹M⁻¹ shape.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- Pointwise: `x^(−2:ℝ) = (x²)⁻¹` for `0 < x` (rpow-literal normalizer). -/
theorem rpow_neg_two_eq_inv_sq {x : ℝ} (hx0 : 0 < x) :
    x ^ ((-2 : ℝ)) = (x^2)⁻¹ := by
  rw [show ((-2 : ℝ)) = -(2 : ℝ) from by norm_num, Real.rpow_neg hx0.le,
    Real.rpow_two]

/-- The inverse-square tail is integrable on `Ioi M`, `M > 0`. -/
theorem inv_sq_integrableOn_Ioi (M : ℝ) (hM : 0 < M) :
    IntegrableOn (fun ξ : ℝ => (ξ^2)⁻¹) (Set.Ioi M) := by
  have h0 := integrableOn_Ioi_rpow_of_lt (show (-2:ℝ) < -1 by norm_num) hM
  apply h0.congr_fun ?_ measurableSet_Ioi
  intro x hx
  exact rpow_neg_two_eq_inv_sq (lt_trans hM hx)

/-- FTC at infinity: `∫_{Ioi M} ξ⁻² = M⁻¹` for `M > 0`. -/
theorem integral_Ioi_inv_sq (M : ℝ) (hM : 0 < M) :
    (∫ ξ in Set.Ioi M, (ξ^2)⁻¹) = M⁻¹ := by
  have hderiv : ∀ x ∈ Set.Ici M, HasDerivAt (fun t : ℝ => -t⁻¹) ((x^2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have hMx : M ≤ x := hx
      exact ne_of_gt (lt_of_lt_of_le hM hMx)
    have h1 : HasDerivAt (fun t : ℝ => t⁻¹) (-(x^2)⁻¹) x := hasDerivAt_inv hx0
    have h2 := h1.neg
    convert h2 using 1
    ring
  have htend : Filter.Tendsto (fun t : ℝ => -t⁻¹) Filter.atTop (nhds 0) := by
    have := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have hneg := this.neg
    simpa using hneg
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv (inv_sq_integrableOn_Ioi M hM) htend
  rw [hFTC]
  simp

/-- Pointwise majorant on Ω-with-floor: ‖f(ξ)‖ ≤ (1/c)·(1+ξ²)⁻¹. -/
theorem norm_cosResolventIntegrand_le (a : ℝ) (s : ℂ) (c : ℝ) (hc : 0 < c)
    (ξ : ℝ) (hfl : c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    ‖cosResolventIntegrand a s ξ‖ ≤ (1/c) * (1 + ξ^2)⁻¹ := by
  have hDpos : (0:ℝ) < c * (1 + ξ^2) := by positivity
  unfold cosResolventIntegrand
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
  have hcos : |Real.cos (ξ * a)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hinvle : ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖⁻¹ ≤ (c * (1 + ξ^2))⁻¹ :=
    inv_anti₀ hDpos hfl
  calc |Real.cos (ξ * a)| * ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖⁻¹
      ≤ 1 * (c * (1 + ξ^2))⁻¹ :=
        mul_le_mul hcos hinvle (by positivity) one_pos.le
    _ = (1/c) * (1 + ξ^2)⁻¹ := by
        rw [one_mul, mul_inv, one_div]

/-- Standalone Ω-integrability certificate on `Ioi 0`. -/
theorem cosResolventIntegrand_integrableOn_Ioi (a : ℝ) (s : ℂ) (c : ℝ)
    (hc : 0 < c)
    (hfl : ∀ ξ : ℝ, c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    IntegrableOn (fun ξ : ℝ => cosResolventIntegrand a s ξ) (Set.Ioi (0:ℝ)) := by
  have hmaj : Integrable (fun ξ : ℝ => (1/c) * (1 + ξ^2)⁻¹)
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    (integrable_inv_one_add_sq.const_mul (1/c)).integrableOn
  refine hmaj.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold cosResolventIntegrand
    apply Measurable.div
    · exact (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_id.mul continuous_const))).measurable
    · exact (continuous_const.add (Complex.continuous_ofReal.pow 2)).measurable
  · filter_upwards with ξ
    exact norm_cosResolventIntegrand_le a s c hc ξ (hfl ξ)

/-- **L1c — the truncation tail**: interval integral vs the full half-line. -/
theorem cosResolvent_interval_vs_Ioi (a M : ℝ) (hM : 0 < M) (s : ℂ)
    (c : ℝ) (hc : 0 < c)
    (hfl : ∀ ξ : ℝ, c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    ‖(∫ ξ in (0:ℝ)..M, cosResolventIntegrand a s ξ)
        - ∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ‖
      ≤ 1 / (c * M) := by
  have hint := cosResolventIntegrand_integrableOn_Ioi a s c hc hfl
  have hintM : IntegrableOn (fun ξ : ℝ => cosResolventIntegrand a s ξ)
      (Set.Ioi M) := hint.mono_set (Set.Ioi_subset_Ioi hM.le)
  have hintOc : IntegrableOn (fun ξ : ℝ => cosResolventIntegrand a s ξ)
      (Set.Ioc (0:ℝ) M) := hint.mono_set Set.Ioc_subset_Ioi_self
  have hsplit : (∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ)
      = (∫ ξ in Set.Ioc (0:ℝ) M, cosResolventIntegrand a s ξ)
        + ∫ ξ in Set.Ioi M, cosResolventIntegrand a s ξ := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hintOc hintM]
    congr 1
    rw [Set.Ioc_union_Ioi_eq_Ioi hM.le]
  have hival : (∫ ξ in (0:ℝ)..M, cosResolventIntegrand a s ξ)
      = ∫ ξ in Set.Ioc (0:ℝ) M, cosResolventIntegrand a s ξ :=
    intervalIntegral.integral_of_le hM.le
  rw [hival, hsplit]
  have hshape : (∫ ξ in Set.Ioc (0:ℝ) M, cosResolventIntegrand a s ξ)
      - ((∫ ξ in Set.Ioc (0:ℝ) M, cosResolventIntegrand a s ξ)
        + ∫ ξ in Set.Ioi M, cosResolventIntegrand a s ξ)
      = -(∫ ξ in Set.Ioi M, cosResolventIntegrand a s ξ) := by ring
  rw [hshape, norm_neg]
  have hmaj_int : IntegrableOn (fun ξ : ℝ => (1/c) * (ξ^2)⁻¹) (Set.Ioi M) :=
    (inv_sq_integrableOn_Ioi M hM).const_mul (1/c)
  have hstep1 : ‖∫ ξ in Set.Ioi M, cosResolventIntegrand a s ξ‖
      ≤ ∫ ξ in Set.Ioi M, (1/c) * (ξ^2)⁻¹ := by
    apply norm_integral_le_of_norm_le hmaj_int
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with ξ hξ
    have hξM : M < ξ := hξ
    have hξ0 : (0:ℝ) < ξ := lt_trans hM hξM
    calc ‖cosResolventIntegrand a s ξ‖
        ≤ (1/c) * (1 + ξ^2)⁻¹ :=
          norm_cosResolventIntegrand_le a s c hc ξ (hfl ξ)
      _ ≤ (1/c) * (ξ^2)⁻¹ := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          apply inv_anti₀ (by positivity)
          linarith [sq_nonneg ξ]
  have hstep2 : (∫ ξ in Set.Ioi M, (1/c) * (ξ^2)⁻¹) = 1 / (c * M) := by
    rw [integral_const_mul, integral_Ioi_inv_sq M hM]
    field_simp
  linarith [hstep1, hstep2.le, hstep2.ge]

#print axioms rpow_neg_two_eq_inv_sq
#print axioms inv_sq_integrableOn_Ioi
#print axioms integral_Ioi_inv_sq
#print axioms norm_cosResolventIntegrand_le
#print axioms cosResolventIntegrand_integrableOn_Ioi
#print axioms cosResolvent_interval_vs_Ioi

end

end RHFormalization
