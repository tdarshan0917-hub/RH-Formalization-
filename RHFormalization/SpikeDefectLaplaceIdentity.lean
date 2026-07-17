-- SENTINEL: L2-v2
import RHFormalization.GalerkinSpikeLaplaceBridge
import RHFormalization.GalerkinBSideLaplace
import RHFormalization.AdaptiveSpikeDefectBound
import Mathlib

/-!
# Per-spike Laplace defect identity (defect-gate L2)

On the right half-plane `0 < Re s`, the transform-side per-spike defect IS
the shifted Laplace transform of the t-domain per-spike defect:

  (1/(2L))·spikeTransform(a,s) − ((L−a)/(2L))·shiftedLaplaceHeatKernelC(a,s)
    = ∫₀^∞ e^{−(s+1/4)t} · (spikeDefect(t,a) : ℂ) dt

Pure wiring of the two banked connectors (`galerkinSpikeKernel_laplace`,
`shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane`) via linearity.
This is what lets `abs_spikeDefect_le` (t-domain) bound the transform defect
on the overlap half-plane.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- The exp-cast window integrand equals the banked `shiftedHeatIntegrand`. -/
theorem window_integrand_eq (a : ℝ) (s : ℂ) :
    (fun t : ℝ => Complex.exp (-(s + (1/4 : ℂ)) * t)
        * ((heatKernelRealScalar t a : ℝ) : ℂ))
      = fun t : ℝ => shiftedHeatIntegrand a s t := by
  funext t
  unfold shiftedHeatIntegrand
  rw [heatKernelG_eq_realScalar t a]
  rw [show Complex.exp (-s * (t:ℂ)) * Complex.exp (-(t:ℂ)/4)
      = Complex.exp (-(s + (1/4 : ℂ)) * t) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- g_N-side integrand as a finite sum of pure modes (banked hfun pattern). -/
theorem spikeKernel_integrand_eq_sum (L a : ℝ) (s : ℂ) :
    (fun t : ℝ => Complex.exp (-(s + (1/4 : ℂ)) * t)
        * ((galerkinSpikeKernel (N := N) L t a : ℝ) : ℂ))
      = fun t : ℝ => ∑ m : Fin N,
          ((galerkinT (N := N) L a m m : ℝ) : ℂ) *
            Complex.exp (-((s + (1/4 : ℂ))
              + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) * t) := by
  funext t
  rw [galerkinSpikeKernel_eq_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hw : heatWeight (N := N) L t m
      = Real.exp (-(t * galerkinLam L (m : ℕ))) := rfl
  rw [hw] at *
  first
    | (rw [← exp_shift_combine (s + (1/4 : ℂ)) (galerkinLam L (m : ℕ)) t]
       push_cast; ring)
    | (have hc := exp_shift_combine (s + (1/4 : ℂ)) (galerkinLam L (m : ℕ)) t
       push_cast at hc ⊢
       rw [← hc]; ring)

/-- g_N-side integrability on the half-plane. -/
theorem spikeKernel_integrand_integrableOn (L a : ℝ) (s : ℂ)
    (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s + (1/4 : ℂ)) * t)
        * ((galerkinSpikeKernel (N := N) L t a : ℝ) : ℂ))
      (Set.Ioi (0:ℝ)) := by
  have hz : 0 < (s + (1/4 : ℂ)).re := by
    simp only [Complex.add_re]
    have h14 : ((1/4 : ℂ)).re = (1/4 : ℝ) := by norm_num
    rw [h14]; linarith
  rw [spikeKernel_integrand_eq_sum]
  refine ?_
  first
    | exact integrable_finset_sum _ (fun m _ =>
        ((spikeMode_integrable (s + (1/4 : ℂ)) hz (galerkinLam L (m : ℕ))
          (by unfold galerkinLam; positivity)).const_mul _))
    | exact MeasureTheory.integrable_finset_sum _ (fun m _ =>
        ((spikeMode_integrable (s + (1/4 : ℂ)) hz (galerkinLam L (m : ℕ))
          (by unfold galerkinLam; positivity)).const_mul _))
    | exact Integrable.sum (fun m =>
        ((spikeMode_integrable (s + (1/4 : ℂ)) hz (galerkinLam L (m : ℕ))
          (by unfold galerkinLam; positivity)).const_mul _))

/-- **L2 — the per-spike Laplace defect identity** on `0 < Re s`. -/
theorem spikeDefectC_laplace (L a : ℝ) (hL : 0 < L) (ha : 0 ≤ a)
    (s : ℂ) (hs : 0 < s.re) :
    ((1 / (2 * L) : ℝ) : ℂ) *
        galerkinSpikeTransform (N := N)
          (fun m => galerkinLam L (m : ℕ)) L a s
      - (((L - a) / (2 * L) : ℝ) : ℂ) * shiftedLaplaceHeatKernelC a s
    = ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-(s + (1/4 : ℂ)) * t) *
          ((((1 / (2 * L)) * galerkinSpikeKernel (N := N) L t a
            - heatKernelRealScalar t a * ((L - a) / (2 * L))) : ℝ) : ℂ) := by
  have hgN := spikeKernel_integrand_integrableOn (N := N) L a s hs
  have hGraw : IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a s t)
      (Set.Ioi (0:ℝ)) :=
    shiftedHeatIntegrand_integrableOn a s hs
  have hG : IntegrableOn (fun t : ℝ => Complex.exp (-(s + (1/4 : ℂ)) * t)
      * ((heatKernelRealScalar t a : ℝ) : ℂ)) (Set.Ioi (0:ℝ)) := by
    rw [window_integrand_eq a s]
    exact hGraw
  symm
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
  rw [integral_sub (hgN.const_mul _) (hG.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  rw [galerkinSpikeKernel_laplace L a s hs]
  congr 1
  rw [window_integrand_eq a s]
  exact congrArg _ (shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane
    a ha s hs).symm

#print axioms window_integrand_eq
#print axioms spikeKernel_integrand_eq_sum
#print axioms spikeKernel_integrand_integrableOn
#print axioms spikeDefectC_laplace

end

end RHFormalization
