-- SENTINEL: quad-remainder-frob-bound-v1
import RHFormalization.QuadRemainderTraceIntegralReduce
import RHFormalization.QuadIntegrandFrobBound
import Mathlib

/-!
# Full quadratic-remainder bound: trace ≤ u · √frobSq(D·V) · √frobSq(V)

Chains `quadRemainder_trace_le_integral_abs` (banked) with the s-free
pointwise bound `quadIntegrand_trace_frob_le` (banked): the s-integral of a
constant majorant over `[0,u]` is `u ·` the constant.
DOWNSTREAM CONSUMER: short-time sector local boundedness along α → h_conv.
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

/-- **Quadratic remainder, fully bounded: N-free, s-integrated.** -/
theorem quadRemainder_trace_frob_le
    (qs : Finset ℕ) (L : ℝ) (hL : 0 < L) (hN : 0 < N)
    (t u : ℝ) (hu : 0 ≤ u) :
    |((Matrix.diagonal fun m => heatWeight L (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal L))
        * ∫ s in (0 : ℝ)..u,
            NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
              * (-(galerkinV (N := N) 1 qs ppWeightReal L))
              * NormedSpace.exp (s • -(galerkinK (N := N) L
                  + galerkinV (N := N) 1 qs ppWeightReal L))).trace|
      ≤ u * (Real.sqrt (frobSq
            ((Matrix.diagonal fun m => heatWeight L (t - u) m)
              * (-(galerkinV (N := N) 1 qs ppWeightReal L))))
          * Real.sqrt (frobSq (galerkinV (N := N) 1 qs ppWeightReal L))) := by
  refine le_trans
    (quadRemainder_trace_le_integral_abs 1 qs ppWeightReal L t u hu) ?_
  set C : ℝ := Real.sqrt (frobSq
        ((Matrix.diagonal fun m => heatWeight L (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal L))))
      * Real.sqrt (frobSq (galerkinV (N := N) 1 qs ppWeightReal L)) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpt : ∀ s ∈ Set.Icc (0:ℝ) u,
      |((Matrix.diagonal fun m => heatWeight L (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal L))
          * (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
              * (-(galerkinV (N := N) 1 qs ppWeightReal L))
              * NormedSpace.exp (s • -(galerkinK (N := N) L
                  + galerkinV (N := N) 1 qs ppWeightReal L)))).trace| ≤ C := by
    intro s hsmem
    rw [hC]
    exact quadIntegrand_trace_frob_le qs L hL hN t u s hsmem.1 hsmem.2
  have hcont : Continuous (fun s : ℝ =>
      |((Matrix.diagonal fun m => heatWeight L (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal L))
          * (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
              * (-(galerkinV (N := N) 1 qs ppWeightReal L))
              * NormedSpace.exp (s • -(galerkinK (N := N) L
                  + galerkinV (N := N) 1 qs ppWeightReal L)))).trace|) := by
    apply Continuous.abs
    first
      | fun_prop
      | (apply Continuous.matrix_trace; fun_prop)
      | continuity
  calc (∫ s in (0:ℝ)..u,
        |((Matrix.diagonal fun m => heatWeight L (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal L))
          * (NormedSpace.exp ((u - s) • -galerkinK (N := N) L)
              * (-(galerkinV (N := N) 1 qs ppWeightReal L))
              * NormedSpace.exp (s • -(galerkinK (N := N) L
                  + galerkinV (N := N) 1 qs ppWeightReal L)))).trace|)
      ≤ ∫ _ in (0:ℝ)..u, C := by
        apply intervalIntegral.integral_mono_on hu
        · exact hcont.intervalIntegrable 0 u
        · exact _root_.intervalIntegrable_const
        · exact hpt
    _ = u * C := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

#print axioms quadRemainder_trace_frob_le

end

end RHFormalization
