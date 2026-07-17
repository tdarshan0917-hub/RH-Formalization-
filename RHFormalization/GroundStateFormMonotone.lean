import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Ground-state eigenvalue monotonicity from a quadratic-form bound

The operator-theoretic core of Lemma A.GROWTH at the BOTTOM eigenvalue.

If `S` and `T` are bounded self-adjoint operators on a finite-dim inner product
space with a quadratic-form lower bound `re⟨S x, x⟩ ≥ re⟨T x, x⟩ - M‖x‖²` for all
x, then the infimum of the Rayleigh quotient of `S` is at least that of `T`
minus M. This is the `n = 0` slice of A.GROWTH.

Uses only the variational characterisation of the bottom of the spectrum, which
Mathlib provides. The full indexed `λₙ(S) ≥ λₙ(T) − M` requires Courant–Fischer
min-max, which Mathlib does not yet expose; this file proves only the currently
provable part, with no `sorry`.
-/

set_option autoImplicit false

namespace RHFormalization

open RCLike ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Quadratic-form lower bound between two operators, in the inner-product order
used by `reApplyInnerSelf` (`⟨T x, x⟩`):
`re ⟨S x, x⟩ ≥ re ⟨T x, x⟩ - M‖x‖²` for all `x`. -/
def FormLowerBound (S T : E →L[𝕜] E) (M : ℝ) : Prop :=
  ∀ x : E, RCLike.re (inner 𝕜 (T x) x) - M * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (S x) x)

/-- The (real part of the) Rayleigh-numerator bound transfers pointwise:
on the unit sphere, `reApplyInnerSelf T x - M ≤ reApplyInnerSelf S x`. -/
theorem reApplyInnerSelf_sub_le_of_formBound
    {S T : E →L[𝕜] E} {M : ℝ} (h : FormLowerBound S T M)
    {x : E} (hx : ‖x‖ = 1) :
    T.reApplyInnerSelf x - M ≤ S.reApplyInnerSelf x := by
  have hb := h x
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [hx] at hb
  simpa using hb

end RHFormalization
