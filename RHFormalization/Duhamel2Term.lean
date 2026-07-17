import RHFormalization.Duhamel2IntegrandSqrtBound

/-!
# Brick 2, Stone 6C-i: the order-2 Duhamel TERM (time integral) + triangle bound
`duhamel2Term t := ∫₀ᵗ duhamel2Integrand u du` — the faithful order-2 Duhamel
term. Triangle bound `|duhamel2Term t| ≤ ∫₀ᵗ |duhamel2Integrand u| du`. Next:
bound RHS by integrable (t-u)^{-1/2}u^{-1/2} (6B'), evaluate Beta convolution
∫₀ᵗ(t-u)^{-1/2}u^{-1/2}=π (6C-iii).
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- The order-2 Duhamel term: time integral of the order-2 integrand. -/
noncomputable def duhamel2Term
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, duhamel2Integrand (N := N) δ qs w L t u

/-- **Stone 6C-i**: triangle bound on the order-2 Duhamel term. -/
theorem abs_duhamel2Term_le_integral_abs
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    |duhamel2Term (N := N) δ qs w L t|
      ≤ ∫ u in (0:ℝ)..t, |duhamel2Integrand (N := N) δ qs w L t u| := by
  unfold duhamel2Term
  exact intervalIntegral.abs_integral_le_integral_abs ht

#print axioms abs_duhamel2Term_le_integral_abs
end
end RHFormalization
