-- SENTINEL: matched-interacting-resolvent-identity-v2
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix

variable {N : ℕ}

/--
Exact resummed second-order resolvent identity.

From

  R₁ - R₀ = -R₀ W R₁

we obtain

  R₀ W R₀
    = -(R₁ - R₀) + R₀ W R₀ W R₁.

The final term retains the full interacting resolvent `R₁`.
-/
theorem matched_resolvent_second_order_identity
    (R0 R1 W : Matrix (Fin N) (Fin N) ℂ)
    (hres : R1 - R0 = -(R0 * W * R1)) :
    R0 * W * R0
      =
    -(R1 - R0) + R0 * W * R0 * W * R1 := by

  have hdiff : R0 - R1 = R0 * W * R1 := by
    calc
      R0 - R1 = -(R1 - R0) := by abel
      _ = -(-(R0 * W * R1)) := by rw [hres]
      _ = R0 * W * R1 := by simp

  have hR0 : R0 = R1 + R0 * W * R1 := by
    calc
      R0 = R1 + (R0 - R1) := by abel
      _ = R1 + R0 * W * R1 := by rw [hdiff]

  have hfirst : R0 * W * R1 = -(R1 - R0) := by
    calc
      R0 * W * R1 = R0 - R1 := hdiff.symm
      _ = -(R1 - R0) := by abel

  calc
    R0 * W * R0
        = R0 * W * (R1 + R0 * W * R1) := by
            exact congrArg (fun X => R0 * W * X) hR0
    _ = R0 * W * R1 + R0 * W * R0 * W * R1 := by
          noncomm_ring
    _ = -(R1 - R0) + R0 * W * R0 * W * R1 := by
          rw [hfirst]

/--
Observable form: left multiplication by `T` preserves the exact
decomposition.
-/
theorem matched_resolvent_second_order_observable
    (T R0 R1 W : Matrix (Fin N) (Fin N) ℂ)
    (hres : R1 - R0 = -(R0 * W * R1)) :
    T * R0 * W * R0
      =
    -(T * (R1 - R0)) + T * R0 * W * R0 * W * R1 := by
  have h := congrArg (fun X => T * X)
    (matched_resolvent_second_order_identity R0 R1 W hres)
  simpa only [mul_add, mul_neg, mul_assoc] using h

#print axioms matched_resolvent_second_order_identity
#print axioms matched_resolvent_second_order_observable

end

end RHFormalization
