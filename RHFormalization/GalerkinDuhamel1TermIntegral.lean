import RHFormalization.GalerkinDuhamel1Term
import Mathlib

/-!
# Order-1 Duhamel TERM (time integral) + triangle bound

`duhamel1Term t := ∫₀ᵗ duhamel1Integrand t u du` — the faithful order-1 Duhamel
term on the genuine position-space operator (`galerkinK + galerkinV`), mirroring
the banked `duhamel2Term`. Triangle bound `|duhamel1Term t| ≤ ∫₀ᵗ |duhamel1Integrand t u| du`.

This is the order-1 analogue of `Duhamel2Term.lean` (green). It is the first
brick of the Dyson identity:
  Tr(e^{-t(K+V)}) = Tr(e^{-tK}) + duhamel1Term + (order ≥ 2).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- The order-1 Duhamel term: time integral of the order-1 integrand
`∫₀ᵗ Tr(e^{-(t-u)K} · galerkinV · e^{-uK}) du`. -/
noncomputable def duhamel1Term
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, duhamel1Integrand (N := N) δ qs w L t u

/-- **Triangle bound on the order-1 Duhamel term.** -/
theorem abs_duhamel1Term_le_integral_abs
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    |duhamel1Term (N := N) δ qs w L t|
      ≤ ∫ u in (0:ℝ)..t, |duhamel1Integrand (N := N) δ qs w L t u| := by
  unfold duhamel1Term
  exact intervalIntegral.abs_integral_le_integral_abs ht

#print axioms duhamel1Term
#print axioms abs_duhamel1Term_le_integral_abs

end
end RHFormalization
