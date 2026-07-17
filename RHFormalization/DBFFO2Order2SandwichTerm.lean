import RHFormalization.DBFFO2BornErrorSplit

/-!
# DBFFO2Order2SandwichTerm

ROUTE CARD
1. Target: O2/O3 order-2 remainder integration layer.
2. Object: `galerkinOrder2SandwichTrace`, the true O1 remainder from the
   full-propagator sandwich split.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright: definitions + triangle inequality for interval integrals.
6. Manuscript: D.OP-BOUND / O1→O2 transition.
7. Consumer: the next bridge bounding `galerkinOrder2SandwichTrace` by the
   existing Duhamel2 / prime-Duhamel bound machinery.

This file does not claim the order-2 estimate. It packages the exact integrated
remainder and reduces its absolute value to the integral of the absolute
pointwise remainder. The pointwise bound is the next brick.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The integrated true order-2 sandwich remainder from O1. -/
noncomputable def galerkinOrder2SandwichTerm
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t,
    galerkinOrder2SandwichTrace (N := N) δ qs w L t u

/-- Triangle bound for the integrated true order-2 sandwich remainder. -/
theorem abs_galerkinOrder2SandwichTerm_le_integral_abs
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    |galerkinOrder2SandwichTerm (N := N) δ qs w L t|
      ≤ ∫ u in (0 : ℝ)..t,
          |galerkinOrder2SandwichTrace (N := N) δ qs w L t u| := by
  unfold galerkinOrder2SandwichTerm
  exact intervalIntegral.abs_integral_le_integral_abs ht

/--
Integrated O1/O2 split using the model heat-kernel term, Born error, and true
order-2 sandwich term.
-/
theorem galerkinDuhamel_trace_identity_model_error_order2
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace
      - (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
      =
      ∫ u in (0 : ℝ)..t,
        (- bornScaledHeatKernelSum qs w L t
          + (- bornError (N := N) δ qs w L t u
              + galerkinOrder2SandwichTrace (N := N) δ qs w L t u)) := by
  have h :=
    galerkinDuhamel_trace_identity_integrated_split
      (N := N) δ qs w L t
  rw [h]
  have hfun :
      (fun u : ℝ =>
        - duhamel1Integrand (N := N) δ qs w L t u
          + galerkinOrder2SandwichTrace (N := N) δ qs w L t u)
      =
      (fun u : ℝ =>
        - bornScaledHeatKernelSum qs w L t
          + (- bornError (N := N) δ qs w L t u
              + galerkinOrder2SandwichTrace (N := N) δ qs w L t u)) := by
    funext u
    exact o1_integrand_eq_model_error_remainder
      (N := N) δ qs w L t u
  rw [hfun]

#print axioms galerkinOrder2SandwichTerm
#print axioms abs_galerkinOrder2SandwichTerm_le_integral_abs
#print axioms galerkinDuhamel_trace_identity_model_error_order2

end

end RHFormalization
