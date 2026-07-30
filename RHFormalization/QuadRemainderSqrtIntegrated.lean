-- SENTINEL: quad-remainder-sqrt-integrated-v2
import RHFormalization.QuadRemainderDiagChainBound
import RHFormalization.HeatSumSqrtBound
import Mathlib

/-!
# Brick (b1): u-integrable sqrt variant of the short-time quadratic bound

The geometric heat factor is not u-integrable near u=t; the banked
`sum_heatWeight_le_sqrt` is. Same diagonal chain, sqrt heat bound:

`|tr(D·(−V)·∫E₁·(−V)·E₂)| ≤ u · (√(π/((t−u)·(π/1)²))/2) · SupVConst²`

N-free, qs-uniform (SupVConst anchor), α-uniform, u-integrable on [0,t).
DOWNSTREAM CONSUMER: the ∫₀ᵗ u-integration brick → transform local
boundedness on Ω-compacts → h_conv.
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

/-- sqrt-variant of the diagonal-chain closer. -/
theorem quadIntegrand_trace_sqrt_le
    (qs : Finset ℕ) (hN : 0 < N)
    (t u s : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) (hut : u < t) :
    |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1)
            * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
                * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
                * NormedSpace.exp (s • -(galerkinK (N := N) 1
                    + galerkinV (N := N) 1 qs ppWeightReal 1))))).trace|
      ≤ (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * SupVConst ^ 2 := by
  have hd : ∀ m : Fin N, 0 ≤ heatWeight (N := N) 1 (t - u) m := by
    intro m
    unfold heatWeight
    exact le_of_lt (Real.exp_pos _)
  set M : Matrix (Fin N) (Fin N) ℝ :=
    (-(galerkinV (N := N) 1 qs ppWeightReal 1)
      * (NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
          * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
          * NormedSpace.exp (s • -(galerkinK (N := N) 1
              + galerkinV (N := N) 1 qs ppWeightReal 1)))) with hM
  have hMdiag : ∀ m : Fin N, |M m m| ≤ SupVConst ^ 2 := by
    intro m
    set e : Fin N → ℝ := (fun k => if k = m then (1:ℝ) else 0) with he
    have hcol := quadWord_mulVec_sumSq_le qs hN
      (by linarith : (0:ℝ) ≤ u - s) hs e
    have hunit : ∑ i : Fin N, (e i) ^ 2 = 1 := by
      rw [he]
      exact unitVec_sumSq m
    rw [hunit, mul_one] at hcol
    have hentry : M m m = (M.mulVec e) m := by
      rw [he]
      exact diag_entry_eq_mulVec_unit M m
    have hcoord : ((M.mulVec e) m) ^ 2 ≤ ∑ i : Fin N, ((M.mulVec e) i) ^ 2 :=
      sq_coord_le_sumSq (M.mulVec e) m
    have hsq : (M m m) ^ 2 ≤ SupVConst ^ 2 * SupVConst ^ 2 := by
      rw [hentry]
      refine le_trans hcoord ?_
      rw [hM]
      exact hcol
    have habs2 : |M m m| ^ 2 ≤ (SupVConst ^ 2) ^ 2 := by
      rw [sq_abs]
      calc (M m m) ^ 2 ≤ SupVConst ^ 2 * SupVConst ^ 2 := hsq
        _ = (SupVConst ^ 2) ^ 2 := by ring
    have hroot := Real.sqrt_le_sqrt habs2
    rw [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (sq_nonneg _)] at hroot
    exact hroot
  have hsum := sum_heatWeight_le_sqrt (N := N) 1 one_pos (t - u)
    (by linarith : (0:ℝ) < t - u)
  calc |Matrix.trace ((Matrix.diagonal
          fun m => heatWeight (N := N) 1 (t - u) m) * M)|
      ≤ ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * |M m m| := by
        rw [show Matrix.trace ((Matrix.diagonal
            fun m => heatWeight (N := N) 1 (t - u) m) * M)
          = ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * M m m from by
          unfold Matrix.trace
          rw [show Matrix.diag ((Matrix.diagonal
              fun m => heatWeight (N := N) 1 (t - u) m) * M)
            = fun m => heatWeight (N := N) 1 (t - u) m * M m m from by
            funext m
            simp [Matrix.diag_apply, Matrix.mul_apply,
              Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq,
              Finset.mem_univ]]]
        calc |∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * M m m|
            ≤ ∑ m : Fin N, |heatWeight (N := N) 1 (t - u) m * M m m| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * |M m m| := by
              refine Finset.sum_congr rfl (fun m _ => ?_)
              rw [abs_mul, abs_of_nonneg (hd m)]
    _ ≤ ∑ m : Fin N, heatWeight (N := N) 1 (t - u) m * SupVConst ^ 2 := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        exact mul_le_mul_of_nonneg_left (hMdiag m) (hd m)
    _ = (∑ m : Fin N, heatWeight (N := N) 1 (t - u) m) * SupVConst ^ 2 := by
        rw [← Finset.sum_mul]
    _ ≤ (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * SupVConst ^ 2 := by
        apply mul_le_mul_of_nonneg_right hsum
        exact sq_nonneg _

/-- **Brick (b1): sqrt-variant simplex bound**, u-integrable near u=t. -/
theorem quadRemainder_trace_sqrt_le
    (qs : Finset ℕ) (hN : 0 < N)
    (t u : ℝ) (hu : 0 ≤ u) (hut : u < t) :
    |((Matrix.diagonal fun m => heatWeight (N := N) 1 (t - u) m)
        * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
        * ∫ s in (0 : ℝ)..u,
            NormedSpace.exp ((u - s) • -galerkinK (N := N) 1)
              * (-(galerkinV (N := N) 1 qs ppWeightReal 1))
              * NormedSpace.exp (s • -(galerkinK (N := N) 1
                  + galerkinV (N := N) 1 qs ppWeightReal 1))).trace|
      ≤ u * ((Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
          * SupVConst ^ 2) := by
  refine le_trans
    (quadRemainder_trace_le_integral_abs 1 qs ppWeightReal 1 t u hu) ?_
  set C : ℝ := (Real.sqrt (Real.pi / ((t - u) * (Real.pi / 1) ^ 2)) / 2)
      * SupVConst ^ 2 with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
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
    exact quadIntegrand_trace_sqrt_le qs hN t u s hsmem.1 hsmem.2 hut
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

#print axioms quadIntegrand_trace_sqrt_le
#print axioms quadRemainder_trace_sqrt_le
