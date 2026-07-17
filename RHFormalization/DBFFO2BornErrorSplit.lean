import RHFormalization.DBFFO1IntegratedTraceDecomposition
import RHFormalization.GalerkinDuhamel1ErrorBound

/-!
# DBFFO2BornErrorSplit

ROUTE CARD
1. Target: O2 first-order/Born error split after the integrated O1 trace identity.
2. Object: `duhamel1Integrand`, the scaled heat-kernel spike sum, and the
   order-2 sandwich trace.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright: algebraic split plus the banked corrected scaled
   `GalerkinDuhamel1ErrorBound`.
6. Manuscript: D.OP-BOUND / O2, short-time first-order trace comparison.
7. Consumer: integrated O2/O3 bound assembly.

This file does not close the full parabola-depth O3 estimate. It banks the
first-order model/error split:

  -duhamel1Integrand + order2
    =
  -scaledHeatKernelSum + (-bornError + order2)

with a pointwise bound on `bornError`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The correctly scaled heat-kernel spike sum matching the first Born term. -/
noncomputable def bornScaledHeatKernelSum
    (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) : ℝ :=
  (2 / L) * (∑ q ∈ qs, w q * heatKernelRealScalar t (Real.log q))

/-- The first-order Born error: Galerkin Duhamel integrand minus scaled heat model. -/
noncomputable def bornError
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) : ℝ :=
  duhamel1Integrand (N := N) δ qs w L t u
    - bornScaledHeatKernelSum qs w L t

/-- Banked corrected scaled first-order error bound, repackaged for O2. -/
theorem bornError_abs_le
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    |bornError (N := N) δ qs w L t u|
      ≤
      |2 / L| *
        (∑ q ∈ qs,
          |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t) := by
  unfold bornError bornScaledHeatKernelSum
  exact abs_duhamel1Integrand_sub_heatKernel_sum_le
    (N := N) δ qs w L t u

/--
Shifted first-order error bound, with the Laplace/shift scalar already included.
-/
theorem shifted_bornError_abs_le
    (σ : ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    |(Real.exp (-σ * t) * Real.exp (-t / 4))
      * bornError (N := N) δ qs w L t u|
      ≤
      (Real.exp (-σ * t) * Real.exp (-t / 4))
        *
        (|2 / L| *
          (∑ q ∈ qs,
            |w q| * finiteSpikeKernelErrorBound (N := N) δ q L t)) := by
  unfold bornError bornScaledHeatKernelSum
  exact abs_shifted_duhamel1Integrand_sub_heatKernel_sum_le
    (N := N) σ δ qs w L t u

/--
Pointwise O1/O2 split of the integrated-trace integrand.

This rewrites the O1 integrand into:
  model heat-kernel spike term + first-order error + order-2 remainder.
-/
theorem o1_integrand_eq_model_error_remainder
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    - duhamel1Integrand (N := N) δ qs w L t u
      + galerkinOrder2SandwichTrace (N := N) δ qs w L t u
    =
    - bornScaledHeatKernelSum qs w L t
      + (- bornError (N := N) δ qs w L t u
          + galerkinOrder2SandwichTrace (N := N) δ qs w L t u) := by
  unfold bornError bornScaledHeatKernelSum
  ring

#print axioms bornScaledHeatKernelSum
#print axioms bornError
#print axioms bornError_abs_le
#print axioms shifted_bornError_abs_le
#print axioms o1_integrand_eq_model_error_remainder

end

end RHFormalization
