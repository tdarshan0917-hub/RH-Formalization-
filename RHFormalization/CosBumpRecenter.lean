import RHFormalization.BumpMatrixElementCosForm
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory intervalIntegral
open scoped Real BigOperators

/-!
# O3 brick 1 — recentering the Gaussian cosine transform.

cosBumpIntegral d q L j = ∫ x in 0..L, cos(j*π*x/L) * gaussBump d (x - log q).
Substitute u = x - log q so the Gaussian sits at 0. First step toward the
closed-form phase × centered-Gaussian transform matchable against starObject's
Dirichlet sum.
-/

/-- Recentered Gaussian cosine transform. -/
theorem cosBumpIntegral_recenter (d : ℝ) (q : ℕ) (L : ℝ) (j : ℝ) :
    cosBumpIntegral d q L j
      = ∫ u in (0 - Real.log q)..(L - Real.log q),
          Real.cos (j * Real.pi * (u + Real.log q) / L) * gaussBump d u := by
  -- Step 1: rewrite the ORIGINAL integrand as g (x - log q).
  have hstep : cosBumpIntegral d q L j
      = ∫ x in (0:ℝ)..L,
          (fun u : ℝ =>
            Real.cos (j * Real.pi * (u + Real.log q) / L) * gaussBump d u)
          (x - Real.log q) := by
    unfold cosBumpIntegral
    apply intervalIntegral.integral_congr
    intro x _
    show Real.cos (j * Real.pi * x / L) * gaussBump d (x - Real.log q)
        = Real.cos (j * Real.pi * ((x - Real.log q) + Real.log q) / L)
            * gaussBump d (x - Real.log q)
    have hx : (x - Real.log q) + Real.log q = x := by ring
    rw [hx]
  rw [hstep]
  -- Step 2: apply the substitution; endpoints 0, L now fixed by the integral.
  exact integral_comp_sub_right
    (fun u : ℝ => Real.cos (j * Real.pi * (u + Real.log q) / L) * gaussBump d u)
    (Real.log q)

#print axioms cosBumpIntegral_recenter

end RHFormalization
