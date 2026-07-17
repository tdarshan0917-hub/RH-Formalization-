import RHFormalization.DispTransformBounded
import RHFormalization.AppendixDKeyFormShortContract
import Mathlib

/-!
# D.LOC sector bound in anchor*factor form (manuscript p174).

The local/cluster residual Q_loc(alpha n) s is the Laplace transform
  ∫_0^{t0} e^{-s t} * gloc_n(t) dt
of the density-normalized local density gloc_n (|Q_loc(t)| ≤ C_loc * t^{3/2}, p174 D.LOC-2,
with C_loc alpha-INDEPENDENT via D.ADM: anchor_integrand_integrable makes the loop integral
finite and anchor_admissible makes (1/2L)*M ≤ 1). disp_transform_bounded then bounds the
transform by e^{sigma0 t0} * ∫ gloc_n ≤ e^{sigma0 t0} * Igbound, the anchor*factor form.

Premises: the transform-form of Q_loc and the density-normalized integral bound on gloc_n
(both manuscript D.LOC/D.ADM content). The local bound is DERIVED, not assumed.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/-- **D.LOC sector bound (factored).** -/
theorem dLoc_sector_bound
    (alpha : ℕ → DFiniteStage)
    (Qloc : DFiniteStage → ℂ → ℂ)
    (gloc : ℕ → ℝ → ℝ) (t0 sigma0 : ℝ) (ht0 : 0 < t0) (hsigma0 : 0 ≤ sigma0)
    (Igbound : ℝ) (hIg_nonneg : 0 ≤ Igbound)
    (hg_nonneg : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) t0, 0 ≤ gloc n t)
    (hg_int : ∀ n, IntervalIntegrable (gloc n) volume 0 t0)
    (hg_intbound : ∀ n, (∫ t in (0:ℝ)..t0, gloc n t) ≤ Igbound)
    (h_transform : ∀ n s, Qloc (alpha n) s
        = ∫ t in (0:ℝ)..t0, Complex.exp (-s * (t : ℂ)) * (gloc n t : ℂ))
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hsK : ∀ s ∈ K, -sigma0 ≤ s.re) :
    ∀ n, ∀ s ∈ K, ‖Qloc (alpha n) s‖ ≤ (1 : ℝ) * (Real.exp (sigma0 * t0) * Igbound) := by
  intro n s hs
  rw [h_transform n s, one_mul]
  have hbound := disp_transform_bounded (gloc n) t0 sigma0 ht0 hsigma0
    (hg_nonneg n) (hg_int n) s (hsK s hs)
  refine le_trans hbound ?_
  apply mul_le_mul_of_nonneg_left (hg_intbound n)
  positivity

#print axioms dLoc_sector_bound

end RHFormalization
