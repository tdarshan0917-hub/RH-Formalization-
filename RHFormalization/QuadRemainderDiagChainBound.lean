-- SENTINEL: quad-remainder-diag-chain-bound-v1
import RHFormalization.QuadRemainderTraceIntegralReduce
import RHFormalization.QuadDiagonalChainBound
import Mathlib

/-!
# Brick (a): simplex-integrated quadratic remainder, N-free

Chains the banked reducer (trace-of-integral ≤ integral-of-abs-trace) with
the banked diagonal-chain closer (s-free pointwise bound). The s-integrand
is constant, so the simplex integral contributes the factor `u`:

`|tr(D·(−V)·∫E₁·(−V)·E₂)| ≤ u · (1 − e^{−(t−u)π²})⁻¹ · SupVConst²`

N-free, qs-uniform (SupVConst anchor), α-uniform.
DOWNSTREAM CONSUMER: transform local boundedness on Ω-compacts → h_conv.
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

/-- **Simplex-integrated quadratic remainder bound, N-free.** -/
theorem quadRemainder_trace_diag_le
    (qs : Finset ℕ) (hN : 0 < N)
    (t u : ℝ) (hu : 0 ≤ u) (hut : u < t) :
    |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
        * ∫ s in (0 : ℝ)..u,
            NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
              * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
              * NormedSpace.exp (s • -(galerkinK (N := N) 1
                  + galerkinV (N := N) 1 qs ppWeightReal 1))).trace|
      ≤ u * ((1 - Real.exp (-((t - u) * (Real.pi / 1) ^ 2)))⁻¹
          * SupVConst ^ 2) := by
  refine le_trans
    (quadRemainder_trace_le_integral_abs 1 qs ppWeightReal 1 t u hu) ?_
  set C : ℝ := (1 - Real.exp (-((t - u) * (Real.pi / 1) ^ 2)))⁻¹
      * SupVConst ^ 2 with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have hexplt : Real.exp (-((t - u) * (Real.pi / 1) ^ 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have : (0:ℝ) < (t - u) * (Real.pi / 1) ^ 2 := by
        have hπ : (0:ℝ) < (Real.pi / 1) ^ 2 := by positivity
        have htu : (0:ℝ) < t - u := by linarith
        positivity
      linarith
    have hpos : (0:ℝ) < 1 - Real.exp (-((t - u) * (Real.pi / 1) ^ 2)) := by
      linarith
    positivity
  have hpt : ∀ s ∈ Set.Icc (0:ℝ) u,
      |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
              * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
              * NormedSpace.exp (s • -(galerkinK (N := N) 1
                  + galerkinV (N := N) 1 qs ppWeightReal 1)))).trace| ≤ C := by
    intro s hsmem
    have hassoc :
        (Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
              * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
              * NormedSpace.exp (s • -(galerkinK (N := N) 1
                  + galerkinV (N := N) 1 qs ppWeightReal 1)))
        = (Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1)
              * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
                  * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
                  * NormedSpace.exp (s • -(galerkinK (N := N) 1
                      + galerkinV (N := N) 1 qs ppWeightReal 1)))) := by
      rw [mul_assoc]
    rw [hassoc, hC]
    exact quadIntegrand_trace_diag_le qs hN t u s hsmem.1 hsmem.2 hut
  have hcont : Continuous (fun s : ℝ =>
      |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
              * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
              * NormedSpace.exp (s • -(galerkinK (N := N) 1
                  + galerkinV (N := N) 1 qs ppWeightReal 1)))).trace|) := by
    apply Continuous.abs
    fun_prop
  calc (∫ s in (0:ℝ)..u,
        |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
              * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
              * NormedSpace.exp (s • -(galerkinK (N := N) 1
                  + galerkinV (N := N) 1 qs ppWeightReal 1)))).trace|)
      ≤ ∫ _ in (0:ℝ)..u, C := by
        apply intervalIntegral.integral_mono_on hu
        · exact hcont.intervalIntegrable 0 u
        · exact _root_.intervalIntegrable_const
        · exact hpt
    _ = u * C := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

#print axioms quadRemainder_trace_diag_le

end

end RHFormalization
