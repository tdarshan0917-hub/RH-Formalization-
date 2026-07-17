import RHFormalization.GalerkinHeatDiagonalGate
import RHFormalization.GalerkinDuhamel1Expansion
import RHFormalization.GalerkinDuhamel1TermSpikeSum
import RHFormalization.Duhamel2Integrand
import Mathlib

namespace RHFormalization

open scoped BigOperators

/-
Goal of this file:
Replace the failed Matrix.exp free-heat object by the clean diagonal heat matrix
`galerkinFreeHeatDiagonal`, then expose the exact trace/Duhamel shape.

This is the next honest Dyson gate.
-/

#check galerkinFreeHeatDiagonal
#check galerkinFreeHeatDiagonal_trace_weight
#check duhamel1Integrand
#check duhamel1Integrand_eq_diag_sum
#check duhamel1Term_eq_t_smul_spike_sum
#check duhamel2Integrand
#check duhamel2Integrand_eq_sum
#check Matrix.trace
#check Matrix.diagonal

#print duhamel1Integrand
#print duhamel2Integrand
#print galerkinFreeHeatDiagonal
#print galerkinV
#print heatWeight

/--
Surface target: order-1 Duhamel integrand should be expressible using the
clean diagonal heat matrix instead of Matrix.exp.

We first expose the exact goal after unfolding.
-/
theorem duhamel1Integrand_diagonal_heat_surface
    {N : ℕ} (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u
      =
    duhamel1Integrand (N := N) δ qs w L t u := by
  -- This file should build. The printed defs above tell us the exact next rewrite.
  rfl

#print axioms duhamel1Integrand_diagonal_heat_surface

end RHFormalization
