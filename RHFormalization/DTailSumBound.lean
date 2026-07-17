import RHFormalization.DTailSpectralBound
import Mathlib

namespace RHFormalization
open Complex
open scoped BigOperators

theorem dTail_sum_bound
    {n : ℕ} (t0 : ℝ) (ht0 : 0 ≤ t0) (s : ℂ) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (delta M : ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, delta ≤ ‖s + (lam i : ℂ)‖)
    (hM : |s.re| ≤ M) :
    ‖∑ i, Complex.exp (-(t0 : ℂ) * (s + (lam i : ℂ))) / (s + (lam i : ℂ))‖
      ≤ Real.exp (t0 * M) * ((1 / delta) * ∑ i, Real.exp (-t0 * lam i)) := by
  have htw := dTail_spectral_termwise t0 ht0 s lam hlam delta M hdelta hgap hM
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => htw i)) ?_
  -- ∑ e^{t0 M}·(1/delta)·e^{-t0 lam i} = e^{t0 M}·(1/delta)·∑ e^{-t0 lam i}
  rw [← Finset.mul_sum]
  apply le_of_eq
  congr 1
  rw [Finset.mul_sum]

#print axioms dTail_sum_bound

end RHFormalization
