-- SENTINEL: matched-scalar-response-kernel-v1
import RHFormalization.MatchedWeightedInteractingGain
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/--
Canonical full-line resolvent kernel in the square-root variable `z`:

  K_z(a) = exp(-a z) / (2 z).

Here `z` represents `sqrt(s + 1/4)`.
-/
def spectralKernelZ (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * z) / ((2 : ℂ) * z)

/--
Closed form of the derivative of `K_z(a)` with respect to `z`.
-/
def spectralKernelZDeriv (a : ℝ) (z : ℂ) : ℂ :=
  -Complex.exp (-(a : ℂ) * z) *
      (((a : ℂ) * z) + 1) /
    ((2 : ℂ) * z ^ 2)

/--
Point-bump first-response kernel:

  J_z(a) = exp(-a z) (a z + 1) / (4 z^3).

Equivalently,

  J_z(a) = exp(-a z) (a + 1/z) / (4 z^2).
-/
def matchedLinearResponseKernelZ (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * z) *
      (((a : ℂ) * z) + 1) /
    ((4 : ℂ) * z ^ 3)

/--
The closed form above is genuinely the complex derivative of
`spectralKernelZ`.
-/
theorem spectralKernelZ_hasDerivAt
    (a : ℝ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt
      (spectralKernelZ a)
      (spectralKernelZDeriv a z)
      z := by
  have hlin :
      HasDerivAt
        (fun w : ℂ => -(a : ℂ) * w)
        (-(a : ℂ))
        z := by
    simpa using
      (hasDerivAt_id z).const_mul (-(a : ℂ))

  have hexp :
      HasDerivAt
        (fun w : ℂ =>
          Complex.exp (-(a : ℂ) * w))
        (Complex.exp (-(a : ℂ) * z) *
          (-(a : ℂ)))
        z := by
    exact hlin.cexp

  have hden :
      HasDerivAt
        (fun w : ℂ => (2 : ℂ) * w)
        (2 : ℂ)
        z := by
    simpa using
      (hasDerivAt_id z).const_mul (2 : ℂ)

  have hquot :=
    hexp.div hden
      (mul_ne_zero (by norm_num) hz)

  change HasDerivAt
    (fun w : ℂ =>
      Complex.exp (-(a : ℂ) * w) /
        ((2 : ℂ) * w))
    (spectralKernelZDeriv a z)
    z

  convert hquot using 1
  unfold spectralKernelZDeriv
  field_simp [hz]
  ring

/--
THE SCALAR STOP/GO IDENTITY:

  J_z(a) = -(1/(2z)) · ∂_z K_z(a).

Thus the matched first response is a spectral derivative of the
canonical kernel, rather than a new independent kernel.
-/
theorem matchedLinearResponseKernelZ_eq_derivative_factor
    (a : ℝ) {z : ℂ} (hz : z ≠ 0) :
    matchedLinearResponseKernelZ a z
      =
    -(((2 : ℂ) * z)⁻¹) *
      spectralKernelZDeriv a z := by
  unfold matchedLinearResponseKernelZ
    spectralKernelZDeriv
  field_simp [hz]
  ring

/--
Equivalent response form, useful when comparing with the earlier
`a + 1/z` calculation.
-/
theorem matchedLinearResponseKernelZ_eq_alt
    (a : ℝ) {z : ℂ} (hz : z ≠ 0) :
    matchedLinearResponseKernelZ a z
      =
    Complex.exp (-(a : ℂ) * z) *
      ((a : ℂ) + z⁻¹) /
      ((4 : ℂ) * z ^ 2) := by
  unfold matchedLinearResponseKernelZ
  field_simp [hz]

#print axioms spectralKernelZ_hasDerivAt
#print axioms matchedLinearResponseKernelZ_eq_derivative_factor
#print axioms matchedLinearResponseKernelZ_eq_alt

end

end RHFormalization
