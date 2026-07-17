-- SENTINEL: E2-v3
import RHFormalization.AdaptiveDefectLaplaceRep
import RHFormalization.RateLaplaceBound
import Mathlib

/-!
# The half-plane norm bound for the adaptive defect (defect-gate E2)

On `0 < Re s`, with `δ := Re s + 1/4`:

  ‖adaptiveGalerkinTransformDefect c n s‖ ≤ adaptiveStageMass n · RateBound(δ)

where RateBound is E1's four-term value. Combined with
`adaptiveStageMass_le_sqrt` and the anchor N/L ≥ n+2, every term of
mass·RateBound → 0: this is the overlap0 rate.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Integrability of `e^{−δt}·rate(t)` (the E1 integrand). -/
theorem exp_mul_stageDefectRate_integrableOn (c : ℝ) (n : ℕ) (δ : ℝ)
    (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ =>
        Real.exp (-δ * t) * adaptiveStageDefectRate c n t)
      (Set.Ioi (0:ℝ)) := by
  set L : ℝ := adaptiveL c n with hLdef
  set R : ℝ := admR n with hRdef
  set M : ℝ := (adaptiveN c n : ℝ) * (Real.pi / L) with hMdef
  have hL : (0:ℝ) < L := adaptiveL_pos c n
  have hI1 : IntegrableOn (fun t : ℝ =>
      (1 / (2 * L)) * Real.exp (-δ * t)) (Set.Ioi (0:ℝ)) :=
    (exp_neg_mul_integrableOn δ hδ).const_mul _
  have hI2 : IntegrableOn (fun t : ℝ => (Real.sqrt Real.pi * R / (2 * L))
      * (t ^ (-(1/2) : ℝ) * Real.exp (-δ * t))) (Set.Ioi (0:ℝ)) :=
    (rpow_neg_half_exp_integrableOn δ hδ).const_mul _
  have hI3 : IntegrableOn (fun t : ℝ =>
      (Real.sqrt (2 * Real.pi) / (2 * Real.pi))
        * (t ^ (-(1/2) : ℝ)
          * (Real.exp (-δ * t) * Real.exp (-(t * M ^ 2) / 2))))
      (Set.Ioi (0:ℝ)) := by
    have h := rpow_neg_half_exp_integrableOn (δ + M ^ 2 / 2) (by positivity)
    refine (h.congr_fun (fun t _ => ?_) measurableSet_Ioi).const_mul _
    rw [← Real.exp_add]
    congr 1
    ring
  have hI4 : IntegrableOn (fun t : ℝ =>
      ((1 + Real.log (adaptiveN c n)) / (2 * Real.pi * L))
        * Real.exp (-δ * t)) (Set.Ioi (0:ℝ)) :=
    (exp_neg_mul_integrableOn δ hδ).const_mul _
  refine (((hI1.add hI2).add hI3).add hI4).congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0:ℝ) < t := ht
  simp only [Pi.add_apply]
  unfold adaptiveStageDefectRate
  rw [← hLdef, ← hRdef]
  rw [sqrt_div_eq_rpow Real.pi t Real.pi_pos.le ht0,
    sqrt_div_eq_rpow (2 * Real.pi) t (by positivity) ht0]
  rw [← hMdef]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  try ring

/-- The weighted t-domain sum in `weightReal` form, absolute value. -/
theorem abs_weighted_defect_sum_le (c : ℝ) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    |∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        q.weightReal * adaptiveSpikeDefectT c n q.center t|
      ≤ adaptiveStageMass n * adaptiveStageDefectRate c n t := by
  calc |∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightReal * adaptiveSpikeDefectT c n q.center t|
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          |q.weightReal * adaptiveSpikeDefectT c n q.center t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC‖ * |adaptiveSpikeDefectT c n q.center t| := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [abs_mul, norm_weightC_eq_abs_weightReal]
    _ ≤ adaptiveStageMass n * adaptiveStageDefectRate c n t := by
        first
          | exact weighted_adaptiveSpikeDefect_sum_le c n t ht
          | exact weighted_adaptiveSpikeDefect_sum_le c n t ht.le
          | exact weighted_adaptiveSpikeDefect_sum_le c n ht t
          | exact weighted_adaptiveSpikeDefect_sum_le (c := c) (n := n)
              (t := t) ht

/-- **E2 — the half-plane norm bound**, `δ := Re s + 1/4`. -/
theorem adaptiveDefect_norm_le (c : ℝ) (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖adaptiveGalerkinTransformDefect c n s‖
      ≤ adaptiveStageMass n *
          ((1 / (2 * adaptiveL c n)) * (1/(s.re + 1/4))
            + (Real.pi * admR n / (2 * adaptiveL c n))
                * (s.re + 1/4) ^ (-(1/2) : ℝ)
            + 1 / ((adaptiveN c n : ℝ) * (Real.pi / adaptiveL c n))
            + ((1 + Real.log (adaptiveN c n))
                / (2 * Real.pi * adaptiveL c n)) * (1/(s.re + 1/4))) := by
  have hδ : (0:ℝ) < s.re + 1/4 := by linarith
  have hmass : (0:ℝ) ≤ adaptiveStageMass n := by
    first
      | exact adaptiveStageMass_nonneg n
      | positivity
      | (unfold adaptiveStageMass
         exact Finset.sum_nonneg fun q _ => norm_nonneg _)
  rw [adaptiveDefect_laplace c n s hs]
  have hg : IntegrableOn (fun t : ℝ => adaptiveStageMass n *
      (Real.exp (-(s.re + 1/4) * t) * adaptiveStageDefectRate c n t))
      (Set.Ioi (0:ℝ)) :=
    (exp_mul_stageDefectRate_integrableOn c n (s.re + 1/4) hδ).const_mul _
  have hmaj : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ‖Complex.exp (-(s + (1/4 : ℂ)) * t) *
          (((∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
              q.weightReal * adaptiveSpikeDefectT c n q.center t) : ℝ) : ℂ)‖
        ≤ adaptiveStageMass n *
            (Real.exp (-(s.re + 1/4) * t)
              * adaptiveStageDefectRate c n t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    have hre : (-(s + (1/4 : ℂ)) * t).re = -(s.re + 1/4) * t := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      norm_num
    rw [norm_mul]
    have hexp : ‖Complex.exp (-(s + (1/4 : ℂ)) * t)‖
        = Real.exp (-(s.re + 1/4) * t) := by
      first
        | rw [Complex.norm_exp, hre]
        | rw [Complex.abs_exp, hre]
        | (simp only [Complex.norm_exp]; rw [hre])
    rw [hexp]
    have hcast : ‖(((∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        q.weightReal * adaptiveSpikeDefectT c n q.center t) : ℝ) : ℂ)‖
        = |∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            q.weightReal * adaptiveSpikeDefectT c n q.center t| := by
      first
        | rw [Complex.norm_real, Real.norm_eq_abs]
        | rw [Complex.norm_ofReal]
        | (simp only [Complex.norm_real]; rw [Real.norm_eq_abs])
        | rw [Complex.norm_ofReal, Real.norm_eq_abs]
    rw [hcast]
    have hsum := abs_weighted_defect_sum_le c n t ht0
    have hexp_pos : (0:ℝ) < Real.exp (-(s.re + 1/4) * t) := Real.exp_pos _
    calc Real.exp (-(s.re + 1/4) * t)
          * |∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
              q.weightReal * adaptiveSpikeDefectT c n q.center t|
        ≤ Real.exp (-(s.re + 1/4) * t)
            * (adaptiveStageMass n * adaptiveStageDefectRate c n t) :=
          mul_le_mul_of_nonneg_left hsum hexp_pos.le
      _ = adaptiveStageMass n *
            (Real.exp (-(s.re + 1/4) * t)
              * adaptiveStageDefectRate c n t) := by ring
  calc ‖∫ t in Set.Ioi (0:ℝ),
          Complex.exp (-(s + (1/4 : ℂ)) * t) *
            (((∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
                q.weightReal * adaptiveSpikeDefectT c n q.center t) : ℝ) : ℂ)‖
      ≤ ∫ t in Set.Ioi (0:ℝ), adaptiveStageMass n *
          (Real.exp (-(s.re + 1/4) * t) * adaptiveStageDefectRate c n t) :=
        MeasureTheory.norm_integral_le_of_norm_le hg hmaj
    _ = adaptiveStageMass n * ∫ t in Set.Ioi (0:ℝ),
          Real.exp (-(s.re + 1/4) * t) * adaptiveStageDefectRate c n t :=
        integral_const_mul _ _
    _ ≤ adaptiveStageMass n *
          ((1 / (2 * adaptiveL c n)) * (1/(s.re + 1/4))
            + (Real.pi * admR n / (2 * adaptiveL c n))
                * (s.re + 1/4) ^ (-(1/2) : ℝ)
            + 1 / ((adaptiveN c n : ℝ) * (Real.pi / adaptiveL c n))
            + ((1 + Real.log (adaptiveN c n))
                / (2 * Real.pi * adaptiveL c n)) * (1/(s.re + 1/4))) :=
        mul_le_mul_of_nonneg_left
          (laplace_stageDefectRate_le c n (s.re + 1/4) hδ) hmass

#print axioms exp_mul_stageDefectRate_integrableOn
#print axioms abs_weighted_defect_sum_le
#print axioms adaptiveDefect_norm_le

end

end RHFormalization
