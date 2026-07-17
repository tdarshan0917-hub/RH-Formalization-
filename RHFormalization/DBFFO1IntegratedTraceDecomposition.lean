import RHFormalization.DBFFO1SandwichTraceDecomposition

/-!
# DBFFO1IntegratedTraceDecomposition

ROUTE CARD
1. Target: O1 integrated trace bridge.
2. Object: the true traced Duhamel identity, with the banked pointwise sandwich split.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright: substitute the pointwise trace split into the traced Duhamel identity.
6. Manuscript: D.OP-BOUND / O1.
7. Consumer: O2/O3 bounds on the Born term and order-2 sandwich remainder.

This file banks:

  Tr(e^{-t(K+V)}) - Tr(e^{-tK})
    = ∫₀ᵗ (-duhamel1Integrand + order2SandwichTrace) du.

The next files split/bound the two integral pieces.
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

/--
Integrated O1 decomposition: the true finite-dimensional trace difference equals
the integral of the Born/free-free term plus the order-2 sandwich remainder.
-/
theorem galerkinDuhamel_trace_identity_integrated_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace
      - (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
      =
      ∫ u in (0 : ℝ)..t,
        (- duhamel1Integrand (N := N) δ qs w L t u
          + galerkinOrder2SandwichTrace (N := N) δ qs w L t u) := by
  have hD :=
    galerkinDuhamel_trace_identity (N := N) δ qs w L t
  rw [hD]
  have hfun :
      (fun u : ℝ =>
        (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) δ qs w L))
          * NormedSpace.exp
            (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace)
      =
      (fun u : ℝ =>
        - duhamel1Integrand (N := N) δ qs w L t u
          + galerkinOrder2SandwichTrace (N := N) δ qs w L t u) := by
    funext u
    exact galerkinSandwich_trace_split (N := N) δ qs w L t u
  rw [hfun]
  ring

#print axioms galerkinDuhamel_trace_identity_integrated_split

end

end RHFormalization
