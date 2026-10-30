import RHFormalization.PrimeGraphTrace
import Mathlib

/-!
# PrimeGraphResolvent — PG-2: finite orbit sum in resolvent form

If `1 - U` is invertible, the truncated orbit sum has the exact closed form
`Σ_{m<M} U^m = (1 - U^M)(1 - U)⁻¹`, hence
`Tr(Λ Σ_{m<M} U^m) = Tr(Λ (1 - U^M)(1 - U)⁻¹)` — the finite-M form of the
prime-graph trace formula `Tr(Λ (1 - U)⁻¹)`.
-/

set_option autoImplicit false

namespace RHFormalization

open Matrix
open scoped BigOperators

/-- Geometric orbit sum in closed form. -/
theorem orbit_sum_closed_form {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (h : IsUnit (1 - U).det) (M : ℕ) :
    (∑ m ∈ Finset.range M, U ^ m) = (1 - U ^ M) * (1 - U)⁻¹ := by
  rw [← geom_sum_mul_neg, mul_assoc, Matrix.mul_nonsing_inv _ h, mul_one]

/-- **PG-2**: weighted orbit trace in resolvent form. -/
theorem trace_orbit_sum_resolvent {n : Type*} [Fintype n] [DecidableEq n]
    (Λ U : Matrix n n ℂ) (h : IsUnit (1 - U).det) (M : ℕ) :
    Matrix.trace (Λ * ∑ m ∈ Finset.range M, U ^ m)
      = Matrix.trace (Λ * ((1 - U ^ M) * (1 - U)⁻¹)) := by
  rw [orbit_sum_closed_form U h M]

#print axioms orbit_sum_closed_form
#print axioms trace_orbit_sum_resolvent

end RHFormalization
