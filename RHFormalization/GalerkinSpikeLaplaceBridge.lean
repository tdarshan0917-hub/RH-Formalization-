import RHFormalization.GalerkinPairingBounds
import RHFormalization.DA2LaplaceResolvent
import Mathlib

/-!
# Spike Laplace bridge — BRICK 3b of the canonical-F route
SENTINEL: laplace-bridge-v2

ROUTE CARD
1. Target: `∫_{Ioi 0} e^{−(s+1/4)t}·g_gal(t,a) dt = galerkinSpikeTransform`
   (μ = galerkinLam) for `0 < Re s` — the last t-domain ↔ transform link.
2. Structural payoff: the transform is a finite rational sum with poles in
   `(−∞,0]` only — Ω-holomorphic by construction; identity on a right
   half-plane + identity theorem is the manuscript's transform-level passage.
3. Per-mode identity = banked `inv_eq_laplace_exp` verbatim.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

open MeasureTheory

variable {N : ℕ}

/-- Cast/combine helper: complex shift times real heat weight is one
exponential. -/
theorem exp_shift_combine (z : ℂ) (lam t : ℝ) :
    Complex.exp (-z * t) * ((Real.exp (-(t * lam)) : ℝ) : ℂ)
      = Complex.exp (-(z + (lam : ℂ)) * t) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Per-mode Laplace value, from the banked resolvent identity. -/
theorem spikeMode_laplace (z : ℂ) (hz : 0 < z.re) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(z + (lam : ℂ)) * t))
      = 1 / (z + (lam : ℂ)) := by
  rw [one_div]
  exact (inv_eq_laplace_exp z lam hlam hz).symm

/-- Per-mode integrability. -/
theorem spikeMode_integrable (z : ℂ) (hz : 0 < z.re) (lam : ℝ) (hlam : 0 ≤ lam) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z + (lam : ℂ)) * t))
      (Set.Ioi (0 : ℝ)) := by
  have hre : (-(z + (lam : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith
  exact integrableOn_exp_mul_complex_Ioi hre 0

/-- **BRICK 3b — THE SPIKE LAPLACE BRIDGE.** The shifted Laplace transform of
the free Galerkin spike kernel equals the finite rational spike transform
(at the live spectrum `galerkinLam`), for `0 < Re s`. -/
theorem galerkinSpikeKernel_laplace (L a : ℝ) (s : ℂ) (hs : 0 < s.re) :
    (∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-(s + (1 / 4 : ℂ)) * t) *
          ((galerkinSpikeKernel (N := N) L t a : ℝ) : ℂ))
      = galerkinSpikeTransform (N := N)
          (fun m => galerkinLam L (m : ℕ)) L a s := by
  set z : ℂ := s + (1 / 4 : ℂ) with hzdef
  have hz : 0 < z.re := by
    rw [hzdef]
    simp only [Complex.add_re]
    have : ((1 / 4 : ℂ)).re = (1 / 4 : ℝ) := by norm_num
    rw [this]
    linarith
  -- rewrite the integrand as a finite sum of pure exponentials
  have hfun : (fun t : ℝ =>
      Complex.exp (-z * t) * ((galerkinSpikeKernel (N := N) L t a : ℝ) : ℂ))
      = fun t : ℝ => ∑ m : Fin N,
          ((galerkinT (N := N) L a m m : ℝ) : ℂ) *
            Complex.exp (-(z + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) * t) := by
    funext t
    rw [galerkinSpikeKernel_eq_sum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hw : heatWeight (N := N) L t m = Real.exp (-(t * galerkinLam L (m : ℕ))) := rfl
    rw [hw] at *
    first
      | (rw [← exp_shift_combine z (galerkinLam L (m : ℕ)) t]; push_cast; ring)
      | (have hc := exp_shift_combine z (galerkinLam L (m : ℕ)) t
         push_cast at hc ⊢
         rw [← hc]; ring)
  rw [hfun]
  -- swap integral and finite sum
  have hint : ∀ m ∈ (Finset.univ : Finset (Fin N)),
      IntegrableOn (fun t : ℝ =>
        ((galerkinT (N := N) L a m m : ℝ) : ℂ) *
          Complex.exp (-(z + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) * t))
        (Set.Ioi (0 : ℝ)) := by
    intro m _
    have hlam : (0 : ℝ) ≤ galerkinLam L (m : ℕ) := by
      unfold galerkinLam; positivity
    exact (spikeMode_integrable z hz (galerkinLam L (m : ℕ)) hlam).const_mul _
  first
    | rw [MeasureTheory.integral_finsetSum Finset.univ hint]
    | rw [MeasureTheory.integral_finset_sum Finset.univ hint]
  -- evaluate each mode
  unfold galerkinSpikeTransform
  refine Finset.sum_congr rfl fun m _ => ?_
  have hlam : (0 : ℝ) ≤ galerkinLam L (m : ℕ) := by
    unfold galerkinLam; positivity
  rw [MeasureTheory.integral_const_mul,
    spikeMode_laplace z hz (galerkinLam L (m : ℕ)) hlam]

#print axioms exp_shift_combine
#print axioms spikeMode_laplace
#print axioms spikeMode_integrable
#print axioms galerkinSpikeKernel_laplace

end

end RHFormalization
