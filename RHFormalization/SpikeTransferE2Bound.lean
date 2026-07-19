-- SENTINEL: spike-transfer-e2-bound-v2
import RHFormalization.QuadTracePointwiseBound
import RHFormalization.SpikeTransferM2Form
import Mathlib

/-! # Core brick 6c-iv-b — THE E₂ BOUND (pillar closer).
`|E₂(t)| ≤ √(N·frobSq V)·(N²·t·√(frobSq V))·t` — quadratic in `t` at
fixed cutoff: the finite-stage D.SPIKE-TRANSFER M=2 remainder estimate. -/

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

/-- The quad trace as a function of `u`. -/
noncomputable def quadTraceFn (qs : Finset ℕ) (L t : ℝ) (u : ℝ) : ℝ :=
  (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
      * (-(galerkinV (N := N) 1 qs ppWeightReal L))
      * (∫ s in (0:ℝ)..u, innerSandwich (N := N) qs L u s)).trace

/-- Pointwise: `|quadTraceFn u| ≤ √(N·fV)·√(N²·(N·u·√fV)²)` — assembled
from 6a, 6c-i/ii and the inner entry bound. -/
theorem quadTraceFn_abs_le (qs : Finset ℕ) (L : ℝ) (hL : 0 < L)
    (t u : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) :
    |quadTraceFn (N := N) qs L t u|
      ≤ Real.sqrt ((N:ℝ) * frobSq (galerkinV (N := N) 1 qs ppWeightReal L))
        * Real.sqrt ((N:ℝ)^2 * ((N:ℝ) * u
            * Real.sqrt (frobSq (galerkinV (N := N) 1 qs ppWeightReal L)))^2) := by
  set V := galerkinV (N := N) 1 qs ppWeightReal L with hVdef
  set D := Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
    with hDdef
  set Inn := ∫ s in (0:ℝ)..u, innerSandwich (N := N) qs L u s with hInn
  have hassoc : quadTraceFn (N := N) qs L t u = ((D * (-V)) * Inn).trace := by
    unfold quadTraceFn
    rw [← hVdef, ← hDdef, ← hInn]
  rw [hassoc]
  have hCS := abs_trace_mul_le_frob (D * (-V)) Inn
  refine le_trans hCS (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · -- frobSq (D * (-V)) ≤ N * frobSq V
    apply Real.sqrt_le_sqrt
    calc frobSq (D * (-V)) ≤ frobSq D * frobSq (-V) := frobSq_mul_le _ _
      _ = frobSq D * frobSq V := by rw [frobSq_neg]
      _ ≤ (N:ℝ) * frobSq V := by
          apply mul_le_mul_of_nonneg_right _ (frobSq_nonneg _)
          rw [hDdef]
          exact frobSq_heat_diagonal_le L (t - u) (by linarith)
  · -- frobSq Inn ≤ N² · (N·u·√fV)²  via entrywise integral bound
    apply Real.sqrt_le_sqrt
    have hcont : Continuous (fun s : ℝ => innerSandwich (N := N) qs L u s) := by
      unfold innerSandwich
      first | fun_prop | continuity
    have hentry : ∀ i j : Fin N,
        |Inn i j| ≤ (N:ℝ) * u * Real.sqrt (frobSq V) := by
      intro i j
      rw [hInn, integral_entry (0:ℝ) u _ hcont i j]
      have hbd : ∀ s ∈ Set.uIoc (0:ℝ) u,
          ‖(innerSandwich (N := N) qs L u s) i j‖
            ≤ (N:ℝ) * Real.sqrt (frobSq V) := by
        intro s hs
        have hsIoc : s ∈ Set.Ioc (0:ℝ) u := by
          rwa [Set.uIoc_of_le hu] at hs
        rw [Real.norm_eq_abs]
        refine le_trans (abs_entry_le_sqrt_frobSq _ i j) ?_
        have hfs := frobSq_innerSandwich_le (N := N) qs L hL u s
          hsIoc.1.le hsIoc.2
        have h1 : frobSq (innerSandwich (N := N) qs L u s)
            ≤ ((N:ℝ) * Real.sqrt (frobSq V))^2 := by
          have hsq : ((N:ℝ) * Real.sqrt (frobSq V))^2
              = (N:ℝ) * frobSq V * (N:ℝ) := by
            rw [mul_pow, Real.sq_sqrt (frobSq_nonneg _)]
            ring
          rw [hsq]
          exact hfs
        calc Real.sqrt (frobSq (innerSandwich (N := N) qs L u s))
            ≤ Real.sqrt (((N:ℝ) * Real.sqrt (frobSq V))^2) :=
              Real.sqrt_le_sqrt h1
          _ = |(N:ℝ) * Real.sqrt (frobSq V)| := Real.sqrt_sq_eq_abs _
          _ = (N:ℝ) * Real.sqrt (frobSq V) := by
              rw [abs_of_nonneg (by positivity)]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
      rw [Real.norm_eq_abs] at hnorm
      have habs : |u - 0| = u := by rw [sub_zero]; exact abs_of_nonneg hu
      rw [habs] at hnorm
      calc |∫ s in (0:ℝ)..u, (innerSandwich (N := N) qs L u s) i j|
          ≤ (N:ℝ) * Real.sqrt (frobSq V) * u := hnorm
        _ = (N:ℝ) * u * Real.sqrt (frobSq V) := by ring
    calc frobSq Inn = ∑ i, ∑ j, (Inn i j)^2 := rfl
      _ ≤ ∑ _i : Fin N, ∑ _j : Fin N,
            ((N:ℝ) * u * Real.sqrt (frobSq V))^2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          refine Finset.sum_le_sum (fun j _ => ?_)
          have h := hentry i j
          nlinarith [abs_nonneg (Inn i j), sq_abs (Inn i j)]
      _ = (N:ℝ)^2 * ((N:ℝ) * u * Real.sqrt (frobSq V))^2 := by
          simp [Finset.sum_const, Finset.card_univ]
          ring

#print axioms quadTraceFn_abs_le

end

end RHFormalization
