import RHFormalization.DispTransformBounded
import RHFormalization.AppendixDKeyFormShortContract
import Mathlib

/-!
# D.DISP sector bound in anchor*factor form (manuscript p175).

The displacement residual Q_disp(alpha n) s is the Laplace transform
  ∫_0^{t0} e^{-s t} * g_n(t) dt
of a nonnegative integrable displacement density g_n (the super-poly majorant, p175).
disp_transform_bounded gives ‖transform‖ ≤ e^{sigma0 * t0} * ∫ g_n. With the integral
bounded by Igbound (the D.DISP estimate, manuscript), this is ≤ 1 * (e^{sigma0 t0} * Igbound),
the anchor*factor form the builder consumes (anchor n = 1).

Premises: the transform-form identification of Q_disp and the integral bound on g_n
(both manuscript D.DISP content). The displacement bound is DERIVED, not assumed.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/-- **D.DISP sector bound (factored).** -/
theorem dDisp_sector_bound
    (alpha : ℕ → DFiniteStage)
    (Qdisp : DFiniteStage → ℂ → ℂ)
    (g : ℕ → ℝ → ℝ) (t0 sigma0 : ℝ) (ht0 : 0 < t0) (hsigma0 : 0 ≤ sigma0)
    (Igbound : ℝ) (hIg_nonneg : 0 ≤ Igbound)
    (hg_nonneg : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) t0, 0 ≤ g n t)
    (hg_int : ∀ n, IntervalIntegrable (g n) volume 0 t0)
    (hg_intbound : ∀ n, (∫ t in (0:ℝ)..t0, g n t) ≤ Igbound)
    (h_transform : ∀ n s, Qdisp (alpha n) s
        = ∫ t in (0:ℝ)..t0, Complex.exp (-s * (t : ℂ)) * (g n t : ℂ))
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hsK : ∀ s ∈ K, -sigma0 ≤ s.re) :
    ∀ n, ∀ s ∈ K, ‖Qdisp (alpha n) s‖ ≤ (1 : ℝ) * (Real.exp (sigma0 * t0) * Igbound) := by
  intro n s hs
  rw [h_transform n s, one_mul]
  have hbound := disp_transform_bounded (g n) t0 sigma0 ht0 hsigma0
    (hg_nonneg n) (hg_int n) s (hsK s hs)
  refine le_trans hbound ?_
  apply mul_le_mul_of_nonneg_left (hg_intbound n)
  positivity

#print axioms dDisp_sector_bound

end RHFormalization
