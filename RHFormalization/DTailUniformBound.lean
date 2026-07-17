import RHFormalization.DTailSumBound
import RHFormalization.DTailDensityFreeBound
import Mathlib

/-!
# D.TAIL uniform bound (manuscript p179-180 combined).

Combines the spectral sum bound (dTail_sum_bound) with the Feynman-Kac
density bound (named hypothesis h_fk, the operator content from p179:
free-Dirichlet domination gives (1/2L)*Tr(e^{-t0 H}) <= (4 pi t0)^{-1/2},
INDEPENDENT of L hence of the cutoff stage).

Result: (1/2L)*‖tail sum‖ <= e^{t0 M}*(1/delta)*(4 pi t0)^{-1/2}, alpha-independent.

h_fk is the genuine Feynman-Kac heat-trace density bound (a PREMISE the manuscript
proves), NOT the residual bound (the conclusion). The residual bound is derived here.
-/

namespace RHFormalization
open Complex
open scoped BigOperators

theorem dTail_uniform_bound
    {n : ℕ} (t0 L : ℝ) (ht0 : 0 ≤ t0) (hL : 0 < L)
    (s : ℂ) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (delta M : ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, delta ≤ ‖s + (lam i : ℂ)‖)
    (hM : |s.re| ≤ M)
    -- Feynman-Kac density bound (the named operator premise, p179):
    (h_fk : (1 / (2 * L)) * (∑ i, Real.exp (-t0 * lam i)) ≤ freeHeatDiagonal t0) :
    (1 / (2 * L)) * ‖∑ i, Complex.exp (-(t0 : ℂ) * (s + (lam i : ℂ))) / (s + (lam i : ℂ))‖
      ≤ Real.exp (t0 * M) * ((1 / delta) * freeHeatDiagonal t0) := by
  have hsum := dTail_sum_bound t0 ht0 s lam hlam delta M hdelta hgap hM
  have h2L : (0:ℝ) < 1 / (2 * L) := by positivity
  -- multiply the sum bound by 1/(2L)
  have hstep : (1 / (2 * L)) * ‖∑ i, Complex.exp (-(t0 : ℂ) * (s + (lam i : ℂ))) / (s + (lam i : ℂ))‖
      ≤ (1 / (2 * L)) * (Real.exp (t0 * M) * ((1 / delta) * ∑ i, Real.exp (-t0 * lam i))) := by
    apply mul_le_mul_of_nonneg_left hsum (le_of_lt h2L)
  refine le_trans hstep ?_
  -- rearrange: (1/2L)*(e^{t0M}*(1/delta)*S) = e^{t0M}*(1/delta)*((1/2L)*S) ≤ e^{t0M}*(1/delta)*freeHeat
  have hrw : (1 / (2 * L)) * (Real.exp (t0 * M) * ((1 / delta) * ∑ i, Real.exp (-t0 * lam i)))
      = Real.exp (t0 * M) * ((1 / delta) * ((1 / (2 * L)) * ∑ i, Real.exp (-t0 * lam i))) := by
    ring
  rw [hrw]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
  apply mul_le_mul_of_nonneg_left h_fk
  positivity

#print axioms dTail_uniform_bound

end RHFormalization
