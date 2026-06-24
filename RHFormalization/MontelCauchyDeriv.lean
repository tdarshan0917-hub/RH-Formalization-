import Mathlib

/-!
# Holomorphic Montel — Node 1b-core: Cauchy estimate ⟹ uniform derivative bound

The complex-analytic heart of Montel. If `f` is holomorphic on an open `U` and bounded
by `M` on the sphere `∂B(z, r)` with `closedBall z r ⊆ U`, then `‖deriv f z‖ ≤ M / r`
(Cauchy's estimate, via Mathlib's `Complex.norm_cderiv_le` + `Complex.cderiv_eq_deriv`).

This is *the* reason a locally-bounded HOLOMORPHIC family is equicontinuous: a sup bound
forces a derivative bound, uniformly across the family.

Part of discharging `HolomorphicMontelConvergence` (D.CAN-REM's last gap, p178).
-/

namespace RHFormalization
open Complex Metric

/-- **Cauchy's estimate (Montel node 1b-core).** -/
theorem norm_deriv_le_of_sphere_bound
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {r M : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hr : 0 < r)
    (hzr : closedBall z r ⊆ U)
    (hM : ∀ w ∈ sphere z r, ‖f w‖ ≤ M) :
    ‖deriv f z‖ ≤ M / r := by
  have hcd : cderiv r f z = deriv f z := cderiv_eq_deriv hU hf hr hzr
  rw [← hcd]
  exact norm_cderiv_le hr hM

#print axioms norm_deriv_le_of_sphere_bound

end RHFormalization
