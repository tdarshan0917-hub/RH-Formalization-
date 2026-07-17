-- SENTINEL: L1b-cos-resolvent-deriv-majorant-v3
import RHFormalization.CosResolventKernelIdentityHalfplane
import Mathlib

/-!
# L1b — Derivative majorant for the cosine-resolvent integrand
f(ξ) = cos(ξa)/(s+1/4+ξ²), s ∈ Ω:
1. `cosResolvent_xi_hasDerivAt` — exact ξ-derivative (quotient rule).
2. `norm_cosResolventXiDeriv_le` — ≤ a/(c(1+ξ²)) + 2ξ/(c²(1+ξ²)²).
3. `integral_norm_cosResolventXiDeriv_le` — ∫₀^B ≤ (a/c)(π/2) + 1/c².
v3: dangling ring/norm_num after self-closing tactics trimmed (E2E rule);
volume annotation on the norm intervalIntegrable family.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- The ξ-derivative in quotient-rule shape. -/
def cosResolventXiDeriv (a : ℝ) (s : ℂ) (ξ : ℝ) : ℂ :=
  (((-Real.sin (ξ * a) * a : ℝ)) : ℂ) / (s + (1/4 : ℂ) + (ξ : ℂ)^2)
    - ((Real.cos (ξ * a) : ℝ) : ℂ) * (((2 * ξ : ℝ)) : ℂ)
        / (s + (1/4 : ℂ) + (ξ : ℂ)^2)^2

/-- **The derivative fact** on Ω (quotient rule; denominator pole-free). -/
theorem cosResolvent_xi_hasDerivAt (a : ℝ) (s : ℂ) (hs : s ∈ Ω) (ξ : ℝ) :
    HasDerivAt (fun x : ℝ => cosResolventIntegrand a s x)
      (cosResolventXiDeriv a s ξ) ξ := by
  have hne := denom_ne_zero_of_mem_Omega hs ξ
  have harg : HasDerivAt (fun x : ℝ => x * a) a ξ := by
    simpa using (hasDerivAt_id ξ).mul_const a
  have hcosC : HasDerivAt (fun x : ℝ => ((Real.cos (x * a) : ℝ) : ℂ))
      (((-Real.sin (ξ * a) * a : ℝ)) : ℂ) ξ := (harg.cos).ofReal_comp
  have hsqC : HasDerivAt (fun x : ℝ => ((x^2 : ℝ) : ℂ)) (((2 * ξ : ℝ)) : ℂ) ξ := by
    have hsqR : HasDerivAt (fun x : ℝ => x^2) (2 * ξ) ξ := by
      simpa using hasDerivAt_pow 2 ξ
    exact hsqR.ofReal_comp
  have hshape : (fun x : ℝ => s + (1/4 : ℂ) + ((x : ℂ))^2)
      = fun x : ℝ => s + (1/4 : ℂ) + ((x^2 : ℝ) : ℂ) := by
    funext x
    push_cast
    ring
  have hD : HasDerivAt (fun x : ℝ => s + (1/4 : ℂ) + ((x : ℂ))^2)
      (((2 * ξ : ℝ)) : ℂ) ξ := by
    rw [hshape]
    exact hsqC.const_add (s + (1/4 : ℂ))
  have hdiv := hcosC.div hD hne
  have hfun : (fun x : ℝ => cosResolventIntegrand a s x)
      = fun x : ℝ => ((Real.cos (x * a) : ℝ) : ℂ)
          / (s + (1/4 : ℂ) + ((x : ℂ))^2) := by
    funext x
    unfold cosResolventIntegrand
    rfl
  rw [hfun]
  convert hdiv using 1
  unfold cosResolventXiDeriv
  field_simp

/-- **Pointwise norm majorant** through the denominator floor. -/
theorem norm_cosResolventXiDeriv_le (a ξ : ℝ) (ha : 0 ≤ a) (hξ : 0 ≤ ξ)
    (s : ℂ) (c : ℝ) (hc : 0 < c)
    (hfl : c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    ‖cosResolventXiDeriv a s ξ‖
      ≤ a * (c * (1 + ξ^2))⁻¹ + 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹ := by
  unfold cosResolventXiDeriv
  have hDpos : (0:ℝ) < c * (1 + ξ^2) := by positivity
  have hnormpos : (0:ℝ) < ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖ := lt_of_lt_of_le hDpos hfl
  refine (norm_sub_le _ _).trans ?_
  have hsin : |Real.sin (ξ * a)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hcos : |Real.cos (ξ * a)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have h1 : ‖(((-Real.sin (ξ * a) * a : ℝ)) : ℂ) / (s + (1/4 : ℂ) + (ξ : ℂ)^2)‖
      ≤ a * (c * (1 + ξ^2))⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
    have hs1 : |-Real.sin (ξ * a) * a| ≤ a := by
      rw [abs_mul, abs_neg]
      calc |Real.sin (ξ * a)| * |a| ≤ 1 * |a| :=
            mul_le_mul_of_nonneg_right hsin (abs_nonneg a)
        _ = a := by rw [one_mul, abs_of_nonneg ha]
    have hinvle : ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖⁻¹ ≤ (c * (1 + ξ^2))⁻¹ :=
      inv_anti₀ hDpos hfl
    exact mul_le_mul hs1 hinvle (by positivity) ha
  have h2 : ‖((Real.cos (ξ * a) : ℝ) : ℂ) * (((2 * ξ : ℝ)) : ℂ)
        / (s + (1/4 : ℂ) + (ξ : ℂ)^2)^2‖
      ≤ 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, norm_pow, div_eq_mul_inv]
    have h2ξ : |2 * ξ| = 2 * ξ := abs_of_nonneg (by linarith)
    have hsqle : (c * (1 + ξ^2))^2 ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖^2 := by
      nlinarith [hfl, hDpos.le, hnormpos.le]
    have hinv2 : (‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖^2)⁻¹ ≤ ((c * (1 + ξ^2))^2)⁻¹ :=
      inv_anti₀ (by positivity) hsqle
    have hpow : ((c * (1 + ξ^2))^2)⁻¹ = (c^2 * (1 + ξ^2)^2)⁻¹ := by
      rw [mul_pow]
    calc |Real.cos (ξ * a)| * |2 * ξ| * (‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖^2)⁻¹
        ≤ 1 * |2 * ξ| * (‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖^2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hcos (abs_nonneg _)
      _ = 2 * ξ * (‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖^2)⁻¹ := by rw [one_mul, h2ξ]
      _ ≤ 2 * ξ * ((c * (1 + ξ^2))^2)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv2 (by linarith)
      _ = 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹ := by rw [hpow]
  linarith

/-- Continuity of the derivative in ξ. -/
theorem cosResolventXiDeriv_continuous (a : ℝ) (s : ℂ) (hs : s ∈ Ω) :
    Continuous (fun ξ : ℝ => cosResolventXiDeriv a s ξ) := by
  unfold cosResolventXiDeriv
  have hDne : ∀ x : ℝ, s + (1/4 : ℂ) + (x : ℂ)^2 ≠ 0 :=
    fun x => denom_ne_zero_of_mem_Omega hs x
  apply Continuous.sub
  · apply Continuous.div
    · exact Complex.continuous_ofReal.comp
        (((Real.continuous_sin.comp (continuous_id.mul continuous_const)).neg).mul
          continuous_const)
    · exact continuous_const.add (Complex.continuous_ofReal.pow 2)
    · exact hDne
  · apply Continuous.div
    · exact (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_id.mul continuous_const))).mul
        (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))
    · exact (continuous_const.add (Complex.continuous_ofReal.pow 2)).pow 2
    · intro x
      exact pow_ne_zero 2 (hDne x)

/-- Telescoping majorant integral: `∫₀^B 2ξ/(1+ξ²)² = 1 − (1+B²)⁻¹`. -/
theorem integral_two_xi_inv_sq (B : ℝ) :
    (∫ ξ in (0:ℝ)..B, 2 * ξ * ((1 + ξ^2)^2)⁻¹) = 1 - (1 + B^2)⁻¹ := by
  have hG : ∀ x ∈ Set.uIcc (0:ℝ) B,
      HasDerivAt (fun t : ℝ => -(1 + t^2)⁻¹) (2 * x * ((1 + x^2)^2)⁻¹) x := by
    intro x _
    have hp : HasDerivAt (fun t : ℝ => t^2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h1 : HasDerivAt (fun t : ℝ => 1 + t^2) (2 * x) x := hp.const_add 1
    have hne : (1 + x^2 : ℝ) ≠ 0 := by positivity
    have hinv := (h1.inv hne).neg
    convert hinv using 1
    field_simp
  have hcont : Continuous (fun x : ℝ => 2 * x * ((1 + x^2)^2)⁻¹) := by
    apply Continuous.mul (continuous_const.mul continuous_id)
    apply Continuous.inv₀
    · exact (continuous_const.add (continuous_pow 2)).pow 2
    · intro x
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    (hcont.intervalIntegrable 0 B)]
  ring_nf

/-- Arctan form of the first majorant integral. -/
theorem integral_inv_one_add_sq_from_zero (B : ℝ) :
    (∫ ξ in (0:ℝ)..B, ((1:ℝ) + ξ^2)⁻¹) = Real.arctan B := by
  rw [integral_inv_one_add_sq]
  simp [Real.arctan_zero]

/-- **The majorant integral bound**: uniform in B. -/
theorem majorant_integral_le (c : ℝ) (hc : 0 < c) (a B : ℝ)
    (ha : 0 ≤ a) :
    (∫ ξ in (0:ℝ)..B,
        (a * (c * (1 + ξ^2))⁻¹ + 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹))
      ≤ (a / c) * (Real.pi / 2) + 1 / c^2 := by
  have hcont1 : Continuous (fun ξ : ℝ => a * (c * (1 + ξ^2))⁻¹) := by
    apply Continuous.mul continuous_const
    apply Continuous.inv₀
    · exact continuous_const.mul (continuous_const.add (continuous_pow 2))
    · intro x
      positivity
  have hcont2 : Continuous (fun ξ : ℝ => 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹) := by
    apply Continuous.mul (continuous_const.mul continuous_id)
    apply Continuous.inv₀
    · exact continuous_const.mul ((continuous_const.add (continuous_pow 2)).pow 2)
    · intro x
      positivity
  rw [intervalIntegral.integral_add (hcont1.intervalIntegrable 0 B)
    (hcont2.intervalIntegrable 0 B)]
  have h1 : (∫ ξ in (0:ℝ)..B, a * (c * (1 + ξ^2))⁻¹)
      = (a / c) * Real.arctan B := by
    have hsh : (fun ξ : ℝ => a * (c * (1 + ξ^2))⁻¹)
        = fun ξ : ℝ => (a / c) * ((1:ℝ) + ξ^2)⁻¹ := by
      funext ξ
      rw [mul_inv]
      ring
    rw [hsh, intervalIntegral.integral_const_mul,
      integral_inv_one_add_sq_from_zero]
  have h2 : (∫ ξ in (0:ℝ)..B, 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹)
      = (1 / c^2) * (1 - (1 + B^2)⁻¹) := by
    have hsh : (fun ξ : ℝ => 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹)
        = fun ξ : ℝ => (1 / c^2) * (2 * ξ * ((1 + ξ^2)^2)⁻¹) := by
      funext ξ
      rw [mul_inv]
      ring
    rw [hsh, intervalIntegral.integral_const_mul, integral_two_xi_inv_sq]
  rw [h1, h2]
  have harc : Real.arctan B ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two B).le
  have hac : (0:ℝ) ≤ a / c := by positivity
  have t1 : (a / c) * Real.arctan B ≤ (a / c) * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left harc hac
  have hb2 : (0:ℝ) < (1 + B^2)⁻¹ := by positivity
  have t2 : (1 / c^2) * (1 - (1 + B^2)⁻¹) ≤ 1 / c^2 := by
    calc (1 / c^2) * (1 - (1 + B^2)⁻¹) ≤ (1 / c^2) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 1 / c^2 := mul_one _
  linarith

/-- **L1b packaged**: the derivative-norm integral bound. -/
theorem integral_norm_cosResolventXiDeriv_le (a B : ℝ) (ha : 0 ≤ a)
    (hB : 0 ≤ B) (s : ℂ) (hs : s ∈ Ω) (c : ℝ) (hc : 0 < c)
    (hfl : ∀ ξ : ℝ, c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    (∫ ξ in (0:ℝ)..B, ‖cosResolventXiDeriv a s ξ‖)
      ≤ (a / c) * (Real.pi / 2) + 1 / c^2 := by
  have hcont := cosResolventXiDeriv_continuous a s hs
  have hnint : IntervalIntegrable (fun ξ : ℝ => ‖cosResolventXiDeriv a s ξ‖)
      volume 0 B := hcont.norm.intervalIntegrable (μ := volume) 0 B
  have hcont1 : Continuous (fun ξ : ℝ => a * (c * (1 + ξ^2))⁻¹) := by
    apply Continuous.mul continuous_const
    apply Continuous.inv₀
    · exact continuous_const.mul (continuous_const.add (continuous_pow 2))
    · intro x
      positivity
  have hcont2 : Continuous (fun ξ : ℝ => 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹) := by
    apply Continuous.mul (continuous_const.mul continuous_id)
    apply Continuous.inv₀
    · exact continuous_const.mul ((continuous_const.add (continuous_pow 2)).pow 2)
    · intro x
      positivity
  have hmint : IntervalIntegrable
      (fun ξ : ℝ => a * (c * (1 + ξ^2))⁻¹ + 2 * ξ * (c^2 * (1 + ξ^2)^2)⁻¹)
      volume 0 B := (hcont1.add hcont2).intervalIntegrable (μ := volume) 0 B
  have hmono := intervalIntegral.integral_mono_on hB hnint hmint
    (fun ξ hξ => norm_cosResolventXiDeriv_le a ξ ha hξ.1 s c hc (hfl ξ))
  exact hmono.trans (majorant_integral_le c hc a B ha)

#print axioms cosResolvent_xi_hasDerivAt
#print axioms norm_cosResolventXiDeriv_le
#print axioms cosResolventXiDeriv_continuous
#print axioms integral_two_xi_inv_sq
#print axioms majorant_integral_le
#print axioms integral_norm_cosResolventXiDeriv_le

end

end RHFormalization
