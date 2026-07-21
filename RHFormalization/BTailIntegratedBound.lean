import RHFormalization.BTailSummedBound
import RHFormalization.BSideHeatKernelLaplaceEnvelope
import RHFormalization.RateLaplaceIntegrals
import Mathlib

/-!
# BTailIntegratedBound — C4: ‖bTail‖ ≤ bTailMass · (1/(2√c)), c = Re s

ROUTE CARD
1. Target: (i) ∫_{Ioi 0} bEnvelope c = 1/(2√c) exactly (clone of the
   banked envelope file's sqrt/Γ-scaling moves + laplace_inv_sqrt_eq);
   (ii) ‖bTail n s‖ ≤ bTailMass n · (1/(2·√(s.re))) for Re s > 0 via
   C3 + norm_integral ≤ integral_norm + tail ≤ full line.
2. Consumer: C5 — confrontation with mainTermIntegral's tail at depth.
3. Raw B on Ω? NO. hstar hypothesis? NONE.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real MeasureTheory Set
open scoped BigOperators

/-- **The envelope integral, evaluated**: `∫₀^∞ (4πt)^{−1/2} e^{−ct} dt = 1/(2√c)`. -/
theorem bEnvelope_integral_eq (c : ℝ) (hc : 0 < c) :
    ∫ t in Ioi (0:ℝ), bEnvelope c t = 1 / (2 * Real.sqrt c) := by
  have hcongr : (∫ t in Ioi (0:ℝ), bEnvelope c t)
      = ∫ t in Ioi (0:ℝ),
          (1 / (2 * Real.sqrt Real.pi)) * (t ^ (-(1/2) : ℝ) * Real.exp (-c * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0:ℝ) < t := ht
    have hsqrt4 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
      rw [show (4:ℝ) * Real.pi * t = (2 * Real.sqrt Real.pi)^2 * t by
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hrpow : t ^ (-(1/2) : ℝ) = 1 / Real.sqrt t := by
      rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow, one_div]
    have hst : Real.sqrt t ≠ 0 := by positivity
    have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
    unfold bEnvelope
    rw [hsqrt4, hrpow]
    have hexp : Real.exp (-(c * t)) = Real.exp (-c * t) := by
      congr 1; ring
    rw [hexp]
    field_simp
  rw [hcongr, MeasureTheory.integral_const_mul, laplace_inv_sqrt_eq c hc]
  have hcrp : c ^ (-(1/2) : ℝ) = 1 / Real.sqrt c := by
    rw [Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hcrp]
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsc : Real.sqrt c ≠ 0 := by positivity
  field_simp

/-- **C4: the integrated B-tail bound** on Re s > 0. -/
theorem bTail_norm_le (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖bTail n s‖ ≤ bTailMass n * (1 / (2 * Real.sqrt s.re)) := by
  unfold bTail
  have hbound : ∀ t ∈ Ioi spikeT0,
      ‖galBIntegrand n s t‖ ≤ bTailMass n * bEnvelope s.re t := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_trans spikeT0_pos ht
    have h := galBIntegrand_norm_le_tailMass n s t ht0
    unfold bEnvelope
    calc ‖galBIntegrand n s t‖
        ≤ bTailMass n * (Real.exp (-s.re * t) * (1 / Real.sqrt (4 * Real.pi * t))) := h
      _ = bTailMass n * (1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-(s.re * t))) := by
          have : Real.exp (-s.re * t) = Real.exp (-(s.re * t)) := by congr 1; ring
          rw [this]; ring
  have hEnvInt : IntegrableOn (fun t => bTailMass n * bEnvelope s.re t)
      (Ioi spikeT0) volume := by
    have hfull : IntegrableOn (fun t => bTailMass n * bEnvelope s.re t)
        (Ioi 0) volume :=
      (bEnvelope_integrable s.re hs).const_mul (bTailMass n)
    exact MeasureTheory.IntegrableOn.mono_set hfull
      (fun t ht => lt_trans spikeT0_pos ht)
  calc ‖∫ t in Ioi spikeT0, galBIntegrand n s t‖
      ≤ ∫ t in Ioi spikeT0, bTailMass n * bEnvelope s.re t := by
        apply MeasureTheory.norm_integral_le_of_norm_le hEnvInt
        exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall hbound)
    _ ≤ ∫ t in Ioi (0:ℝ), bTailMass n * bEnvelope s.re t := by
        apply MeasureTheory.setIntegral_mono_set
        · exact (bEnvelope_integrable s.re hs).const_mul (bTailMass n)
        · filter_upwards with t
          exact mul_nonneg (bTailMass_nonneg n) (by unfold bEnvelope; positivity)
        · exact HasSubset.Subset.eventuallyLE (fun t ht => lt_trans spikeT0_pos ht)
    _ = bTailMass n * ∫ t in Ioi (0:ℝ), bEnvelope s.re t :=
        MeasureTheory.integral_const_mul _ _
    _ = bTailMass n * (1 / (2 * Real.sqrt s.re)) := by
        rw [bEnvelope_integral_eq s.re hs]

#print axioms bEnvelope_integral_eq
#print axioms bTail_norm_le

end

end RHFormalization
