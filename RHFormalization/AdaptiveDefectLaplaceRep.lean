-- SENTINEL: L3-v2
import RHFormalization.SpikeDefectLaplaceIdentity
import RHFormalization.AdaptiveWeightedDefectSum
import Mathlib

/-!
# The adaptive defect as a Laplace transform (defect-gate L3)

On `0 < Re s`:

  adaptiveGalerkinTransformDefect c n s
    = ∫₀^∞ e^{−(s+1/4)t} · (Σ_q weightReal_q · adaptiveSpikeDefectT c n a_q t : ℂ) dt

Sum of the L2 per-spike identity via linearity.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Per-spike integrability of the L2 integrand (difference form). -/
theorem spikeDefect_integrand_integrableOn {N : ℕ} (L a : ℝ)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s + (1/4 : ℂ)) * t) *
        ((((1 / (2 * L)) * galerkinSpikeKernel (N := N) L t a
          - heatKernelRealScalar t a * ((L - a) / (2 * L))) : ℝ) : ℂ))
      (Set.Ioi (0:ℝ)) := by
  have hG : IntegrableOn (fun t : ℝ => Complex.exp (-(s + (1/4 : ℂ)) * t)
      * ((heatKernelRealScalar t a : ℝ) : ℂ)) (Set.Ioi (0:ℝ)) := by
    rw [window_integrand_eq a s]
    exact shiftedHeatIntegrand_integrableOn a s hs
  have hsplit : (fun t : ℝ => Complex.exp (-(s + (1/4 : ℂ)) * t) *
        ((((1 / (2 * L)) * galerkinSpikeKernel (N := N) L t a
          - heatKernelRealScalar t a * ((L - a) / (2 * L))) : ℝ) : ℂ))
      = fun t : ℝ =>
        ((1 / (2 * L) : ℝ) : ℂ) *
            (Complex.exp (-(s + (1/4 : ℂ)) * t)
              * ((galerkinSpikeKernel (N := N) L t a : ℝ) : ℂ))
          - (((L - a) / (2 * L) : ℝ) : ℂ) *
            (Complex.exp (-(s + (1/4 : ℂ)) * t)
              * ((heatKernelRealScalar t a : ℝ) : ℂ)) := by
    funext t
    push_cast
    ring
  rw [hsplit]
  exact ((spikeKernel_integrand_integrableOn L a s hs).const_mul _).sub
    (hG.const_mul _)

/-- The adaptive per-spike integrand, defect form, is integrable. -/
theorem adaptiveSpikeDefect_integrand_integrableOn (c : ℝ) (n : ℕ)
    (a : ℝ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s + (1/4 : ℂ)) * t) *
        ((adaptiveSpikeDefectT c n a t : ℝ) : ℂ)) (Set.Ioi (0:ℝ)) := by
  have h := spikeDefect_integrand_integrableOn (N := adaptiveN c n)
    (adaptiveL c n) a s hs
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  unfold adaptiveSpikeDefectT
  rfl

/-- **L3 — the adaptive defect Laplace representation** on `0 < Re s`. -/
theorem adaptiveDefect_laplace (c : ℝ) (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    adaptiveGalerkinTransformDefect c n s
      = ∫ t in Set.Ioi (0:ℝ),
          Complex.exp (-(s + (1/4 : ℂ)) * t) *
            (((∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
                q.weightReal * adaptiveSpikeDefectT c n q.center t) : ℝ) : ℂ) := by
  have hL : (0:ℝ) < adaptiveL c n := adaptiveL_pos c n
  -- Step 1: the defect as a per-spike bracket sum
  have hstep1 : adaptiveGalerkinTransformDefect c n s
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC *
            (((1 / (2 * adaptiveL c n) : ℝ) : ℂ) *
                galerkinSpikeTransform (N := adaptiveN c n)
                  (fun m => galerkinLam (adaptiveL c n) (m : ℕ))
                  (adaptiveL c n) q.center s
              - (((adaptiveL c n - q.center) / (2 * adaptiveL c n) : ℝ) : ℂ) *
                  shiftedLaplaceHeatKernelC q.center s) := by
    unfold adaptiveGalerkinTransformDefect adaptiveFreePairedTransform
      decodedOneLetterTransform windowedCanonicalPackage
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hstep1]
  -- Step 2: each bracket via L2, landing in DEFECT form
  have hstep2 : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      q.weightC *
          (((1 / (2 * adaptiveL c n) : ℝ) : ℂ) *
              galerkinSpikeTransform (N := adaptiveN c n)
                (fun m => galerkinLam (adaptiveL c n) (m : ℕ))
                (adaptiveL c n) q.center s
            - (((adaptiveL c n - q.center) / (2 * adaptiveL c n) : ℝ) : ℂ) *
                shiftedLaplaceHeatKernelC q.center s)
        = ∫ t in Set.Ioi (0:ℝ),
            q.weightC * (Complex.exp (-(s + (1/4 : ℂ)) * t) *
              ((adaptiveSpikeDefectT c n q.center t : ℝ) : ℂ)) := by
    intro q _
    rw [spikeDefectC_laplace (N := adaptiveN c n) (adaptiveL c n) q.center
      hL (center_nonneg q) s hs]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    unfold adaptiveSpikeDefectT
    rfl
  rw [Finset.sum_congr rfl hstep2]
  -- Step 3: swap sum and integral (defect-form integrability)
  rw [← MeasureTheory.integral_finsetSum
    (activePrimePowerPairsCenterBelow (admR n))
    (fun q _ =>
      (adaptiveSpikeDefect_integrand_integrableOn c n q.center s hs).const_mul
        q.weightC)]
  -- Step 4: integrand identity
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [PrimePowerPair.weightC]
  push_cast
  ring

#print axioms spikeDefect_integrand_integrableOn
#print axioms adaptiveSpikeDefect_integrand_integrableOn
#print axioms adaptiveDefect_laplace

end

end RHFormalization
