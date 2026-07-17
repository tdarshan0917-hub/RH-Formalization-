import RHFormalization.GalerkinCanonicalFHolo
import Mathlib

/-!
# Paired perturbed Laplace bridge — BRICK 7 of the canonical-F route
SENTINEL: paired-perturbed-laplace-v1

ROUTE CARD
1. `pairedPerturbedHeatTrace`: the t-domain paired perturbed heat functional
   in eigen-sum form — `Σᵢ ⟨eᵢ, T eᵢ⟩·e^{−tλᵢ(H)}` — the finite analogue of
   `Tr(e^{−tH}·T)` (basis-free matrix-exp identity is a separate later
   bridge; the eigen-sum IS the analytic object the sectors consume).
2. THE BRIDGE: its shifted Laplace transform equals
   `pairedPerturbedSpikeTransform` for `0 < Re s` — structural copy of the
   banked Brick 3b, per-mode via banked `spikeMode_laplace`.
3. With Brick 6's holomorphy this completes the perturbed F-side wiring:
   t-domain paired functional ↔ Ω-holomorphic rational transform.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

open MeasureTheory

variable {N : ℕ}

/-- **Paired perturbed heat trace** (eigen-sum form): the displacement-paired
heat functional of the genuine perturbed operator. -/
def pairedPerturbedHeatTrace (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) : ℂ :=
  ∑ i : Fin N,
    pairedEigenCoeff (N := N) μ hV T i *
      Complex.exp (-(t : ℂ) * ((perturbedEigenvalues μ hV i : ℝ) : ℂ))

/-- Integrand regroup: shift times mode exponential is one exponential. -/
theorem paired_exp_combine (z : ℂ) (lam t : ℝ) :
    Complex.exp (-z * t) * Complex.exp (-(t : ℂ) * ((lam : ℝ) : ℂ))
      = Complex.exp (-(z + (lam : ℂ)) * t) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **BRICK 7 — THE PAIRED PERTURBED LAPLACE BRIDGE.** The shifted Laplace
transform of the paired perturbed heat trace equals the paired perturbed
spike transform, for `0 < Re s` and nonnegative perturbed spectrum. -/
theorem pairedPerturbedHeatTrace_laplace (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues μ hV i)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-(s + (1 / 4 : ℂ)) * t) *
          pairedPerturbedHeatTrace (N := N) μ hV T t)
      = pairedPerturbedSpikeTransform (N := N) μ hV T s := by
  set z : ℂ := s + (1 / 4 : ℂ) with hzdef
  have hz : 0 < z.re := by
    rw [hzdef]
    simp only [Complex.add_re]
    have : ((1 / 4 : ℂ)).re = (1 / 4 : ℝ) := by norm_num
    rw [this]
    linarith
  have hfun : (fun t : ℝ =>
      Complex.exp (-z * t) * pairedPerturbedHeatTrace (N := N) μ hV T t)
      = fun t : ℝ => ∑ i : Fin N,
          pairedEigenCoeff (N := N) μ hV T i *
            Complex.exp (-(z + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)) * t) := by
    funext t
    unfold pairedPerturbedHeatTrace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← paired_exp_combine z (perturbedEigenvalues μ hV i) t]
    ring
  rw [hfun]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      IntegrableOn (fun t : ℝ =>
        pairedEigenCoeff (N := N) μ hV T i *
          Complex.exp (-(z + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)) * t))
        (Set.Ioi (0 : ℝ)) := by
    intro i _
    exact (spikeMode_integrable z hz (perturbedEigenvalues μ hV i)
      (hpos i)).const_mul _
  first
    | rw [MeasureTheory.integral_finsetSum Finset.univ hint]
    | rw [MeasureTheory.integral_finset_sum Finset.univ hint]
  unfold pairedPerturbedSpikeTransform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul,
    spikeMode_laplace z hz (perturbedEigenvalues μ hV i) (hpos i)]

/-- At `t = 0` the paired heat trace is the trace of the observable —
consumes Brick 6's resummation identity. -/
theorem pairedPerturbedHeatTrace_zero (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ) :
    pairedPerturbedHeatTrace (N := N) μ hV T 0
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
          (Matrix.toEuclideanLin T) := by
  unfold pairedPerturbedHeatTrace
  rw [← pairedEigenCoeff_sum_eq_trace μ hV T]
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_num

#print axioms pairedPerturbedHeatTrace
#print axioms paired_exp_combine
#print axioms pairedPerturbedHeatTrace_laplace
#print axioms pairedPerturbedHeatTrace_zero
end

end RHFormalization
