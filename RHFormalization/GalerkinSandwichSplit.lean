import RHFormalization.GalerkinDuhamelIdentity
import RHFormalization.GalerkinFreeHeatDiagonal
import RHFormalization.GalerkinDuhamel1Term
import Mathlib

/-!
# Sandwich split: order-1 free-free + order-2 remainder.

Substituting `exp(u•(-(K+V))) = exp(u•(-K)) + Duhamel_tail` into the sandwich
`exp((t-u)(-K))·(-V)·exp(u(-(K+V)))` splits it into:
  - order-1 free-free: `exp((t-u)(-K))·(-V)·exp(u(-K))`  [= -duhamel1Integrand form]
  - order-2 remainder: `exp((t-u)(-K))·(-V)·Duhamel_tail`  [two V's, Stone 8 bounds it]
-/

set_option autoImplicit false
namespace RHFormalization
noncomputable section
open Matrix MeasureTheory
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- **Sandwich split.** The Dyson sandwich = order-1 free-free term + order-2 remainder,
by substituting the Duhamel identity into the perturbed propagator. -/
theorem galerkinSandwich_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
      = NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) δ qs w L))
          * NormedSpace.exp (u • (-(galerkinK (N := N) L)))
        + NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
          * (-(galerkinV (N := N) δ qs w L))
          * (∫ r in (0:ℝ)..u,
              NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
                * (-(galerkinV (N := N) δ qs w L))
                * NormedSpace.exp (r • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))) := by
  -- substitute exp(u•(-(K+V))) = exp(u•(-K)) + ∫... from the Duhamel identity
  have hid := galerkinDuhamel_identity (N := N) δ qs w L u
  have hsub : NormedSpace.exp (u • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
      = NormedSpace.exp (u • (-(galerkinK (N := N) L)))
        + ∫ r in (0:ℝ)..u,
            NormedSpace.exp ((u - r) • (-(galerkinK (N := N) L)))
              * (-(galerkinV (N := N) δ qs w L))
              * NormedSpace.exp (r • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L))) := by
    rw [← hid]
    first
      | ring
      | abel
      | (rw [add_comm]; abel)
      | (rw [eq_comm, add_comm]
         first | exact (add_sub_cancel _ _).symm | abel | ring)
      | omega
      | rfl
  rw [hsub, mul_add]

#print axioms galerkinSandwich_split
