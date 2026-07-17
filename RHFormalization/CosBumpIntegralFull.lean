import RHFormalization.IntegralCosGaussBump
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory
open scoped Real BigOperators

/-!
# O3 brick 6 — full-line closed form of the recentered cosine-Gaussian-bump integral.
-/

/-- Helper: bounded-trig × gaussBump is integrable over ℝ. -/
theorem integrable_trig_mul_gaussBump (δ : ℝ) (hδ : 0 < δ) (a : ℝ)
    (g : ℝ → ℝ) (hg : ∀ x, |g x| ≤ 1) (hgm : Measurable g) :
    Integrable (fun u : ℝ => g (a * u) * gaussBump δ u) := by
  have hc : (0 : ℝ) < 1 / (2 * δ ^ 2) := by positivity
  have hgauss : Integrable (fun u : ℝ => Real.exp (-(1 / (2 * δ ^ 2)) * u ^ 2)) :=
    integrable_exp_neg_mul_sq hc
  have hrw : (fun u : ℝ => g (a * u) * gaussBump δ u)
      = (fun u : ℝ => (1 / Real.sqrt (2 * Real.pi * δ ^ 2))
          * (g (a * u) * Real.exp (-(1 / (2 * δ ^ 2)) * u ^ 2))) := by
    funext u; unfold gaussBump
    rw [show (-u ^ 2 / (2 * δ ^ 2)) = (-(1 / (2 * δ ^ 2)) * u ^ 2) by ring]; ring
  rw [hrw]
  apply Integrable.const_mul
  have hmeas : AEStronglyMeasurable (fun u : ℝ => g (a * u)) volume :=
    (hgm.comp (measurable_const_mul a)).aestronglyMeasurable
  have hbound : ∀ᵐ u : ℝ, ‖g (a * u)‖ ≤ 1 := by
    filter_upwards with u; rw [Real.norm_eq_abs]; exact hg (a * u)
  exact (hgauss.bdd_mul (c := 1) hmeas hbound).congr (by filter_upwards with u; ring)

/-- Sine transform of the Gaussian bump vanishes (oddness). -/
theorem integral_sin_mul_gaussBump (δ : ℝ) (hδ : 0 < δ) (a : ℝ) :
    (∫ u : ℝ, Real.sin (a * u) * gaussBump δ u) = 0 := by
  set f : ℝ → ℝ := fun u => Real.sin (a * u) * gaussBump δ u with hf
  have hodd : ∀ u : ℝ, f (-u) = - f u := by
    intro u; simp only [hf]
    rw [show a * -u = -(a * u) by ring, Real.sin_neg]
    unfold gaussBump
    rw [show (-u) ^ 2 = u ^ 2 by ring]; ring
  have hrefl : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := integral_neg_eq_self f volume
  have hstep : (∫ x : ℝ, f (-x)) = - ∫ x : ℝ, f x := by
    rw [show (fun x : ℝ => f (-x)) = (fun x : ℝ => - f x) from funext hodd, integral_neg]
  rw [hrefl] at hstep; linarith [hstep]

/-- The full-line recentered cosine-Gaussian-bump integral. -/
noncomputable def cosBumpIntegralFull (δ : ℝ) (q : ℕ) (L : ℝ) (j : ℝ) : ℝ :=
  ∫ u : ℝ, Real.cos (j * Real.pi * (u + Real.log q) / L) * gaussBump δ u

/-- **Closed form** of the full-line recentered cosine-Gaussian-bump integral. -/
theorem cosBumpIntegralFull_closed (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (j : ℝ) :
    cosBumpIntegralFull δ q L j
      = Real.cos (j * Real.pi * Real.log q / L)
          * Real.exp (-((j * Real.pi / L) ^ 2 * δ ^ 2) / 2) := by
  unfold cosBumpIntegralFull
  set A : ℝ := j * Real.pi / L with hA
  set B : ℝ := j * Real.pi * Real.log q / L with hB
  have hpt : ∀ u : ℝ,
      Real.cos (j * Real.pi * (u + Real.log q) / L) * gaussBump δ u
        = Real.cos B * (Real.cos (A * u) * gaussBump δ u)
          - Real.sin B * (Real.sin (A * u) * gaussBump δ u) := by
    intro u
    have harg : j * Real.pi * (u + Real.log q) / L = A * u + B := by rw [hA, hB]; ring
    rw [harg, Real.cos_add]; ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hcC : Integrable (fun u : ℝ => Real.cos (A * u) * gaussBump δ u) :=
    integrable_trig_mul_gaussBump δ hδ A Real.cos (fun x => Real.abs_cos_le_one x) Real.continuous_cos.measurable
  have hcS : Integrable (fun u : ℝ => Real.sin (A * u) * gaussBump δ u) :=
    integrable_trig_mul_gaussBump δ hδ A Real.sin (fun x => Real.abs_sin_le_one x) Real.continuous_sin.measurable
  rw [integral_sub (hcC.const_mul _) (hcS.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_cos_mul_gaussBump δ hδ A, integral_sin_mul_gaussBump δ hδ A]
  rw [hA]; ring

#print axioms cosBumpIntegralFull_closed

end RHFormalization
