import RHFormalization.GalerkinDuhamelTraceIdentity
import RHFormalization.GalerkinSandwichSplit
import RHFormalization.GalerkinOrder1TraceIdent
import RHFormalization.DBFFStarOffParabolaBound

/-!
# DBFFO1SandwichTraceDecomposition

ROUTE CARD
1. Target: O1, first concrete trace-level bridge.
2. Object: the true Duhamel sandwich trace from `galerkinDuhamel_trace_identity`.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright: algebraic consequence of `galerkinSandwich_split` and
   `galerkinOrder1FreeFree_trace_eq`.
6. Manuscript: D.OP-BOUND / O1, trace identity expressing the compensated
   trace as first Born/free-free term plus higher-order Duhamel remainder.
7. Consumer: integrated O1 trace identity, then O2/O3 bounds.

This file only banks the pointwise-in-`u` trace split:

  full sandwich trace =
    - duhamel1Integrand + order2 sandwich trace.

The interval-integrated version is the next brick.
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

/-- The order-2 / higher Duhamel sandwich trace remainder. -/
noncomputable def galerkinOrder2SandwichTrace
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) : ℝ :=
  (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
      * (-(galerkinV (N := N) δ qs w L))
      * (∫ r in (0 : ℝ)..u,
          NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp
              (r • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))))).trace

/--
Pointwise O1 trace decomposition.

The true sandwich trace splits into the free-free Born term and the order-2
sandwich remainder.
-/
theorem galerkinSandwich_trace_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace
      =
        - duhamel1Integrand (N := N) δ qs w L t u
        + galerkinOrder2SandwichTrace (N := N) δ qs w L t u := by
  have hsplit :=
    galerkinSandwich_split (N := N) δ qs w L t u
  have htr := congrArg Matrix.trace hsplit
  first
    | rw [Matrix.trace_add] at htr
    | simp only [Matrix.trace_add] at htr
    | simp at htr
  have hff :=
    galerkinOrder1FreeFree_trace_eq (N := N) δ qs w L t u
  rw [hff] at htr
  simpa [galerkinOrder2SandwichTrace] using htr

#print axioms galerkinOrder2SandwichTrace
#print axioms galerkinSandwich_trace_split

end

end RHFormalization
