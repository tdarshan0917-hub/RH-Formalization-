-- SENTINEL: DIAGTRACE-v4
import RHFormalization.HeatContractionBound
import Mathlib

/-!
# DiagTracePairingBound — B3 stone 3a

CONSUMER: the remainder bound ‖Z‖ = |Tr(heatDiag·(−V)·e^{−u(K+V)}·T)|,
which feeds `hr` of `seam_bdd_of_parts` (SEAMASM), which feeds the banked
`h_ctail_le_of_seam_bdd` (B2CONN), which feeds GATE → RH.

THE LEMMA: for a nonneg diagonal d and any real matrix M (linftyOp norm),

    |Tr(diagonal d * M)| ≤ (Σ m, d m) * ‖M‖

Proof from primitives: Tr(diag(d)·M) = Σ m, d m * M m m, and each diagonal
entry |M m m| ≤ Σ_j |M m j| ≤ ‖M‖ (the linftyOp sup-row-sum). This is the
N-free mechanism: the dimension never appears, only the heat mass Σ d.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RHFormalization

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Diagonal entry bounded by the linftyOp norm: |M m m| ≤ ‖M‖. -/
theorem abs_diag_entry_le_linfty_norm
    (M : Matrix (Fin N) (Fin N) ℝ) (m : Fin N) :
    |M m m| ≤ ‖M‖ := by
  have hrow : |M m m| ≤ ∑ j : Fin N, ‖M m j‖ := by
    have : ‖M m m‖ ≤ ∑ j : Fin N, ‖M m j‖ :=
      Finset.single_le_sum (f := fun j => ‖M m j‖)
        (fun j _ => norm_nonneg _) (Finset.mem_univ m)
    simpa [Real.norm_eq_abs] using this
  have hle : (∑ j : Fin N, ‖M m j‖) ≤ ‖M‖ := by
    have hdef := Matrix.linfty_opNorm_def M
    rw [hdef]
    have hsup : (∑ j : Fin N, ‖M m j‖₊)
        ≤ Finset.univ.sup (fun i => ∑ j : Fin N, ‖M i j‖₊) :=
      Finset.le_sup (f := fun i => ∑ j : Fin N, ‖M i j‖₊) (Finset.mem_univ m)
    have hcast := (NNReal.coe_le_coe).mpr hsup
    calc (∑ j : Fin N, ‖M m j‖)
        = ((∑ j : Fin N, ‖M m j‖₊ : NNReal) : ℝ) := by
          simp [NNReal.coe_sum, coe_nnnorm]
      _ ≤ ((Finset.univ.sup (fun i => ∑ j : Fin N, ‖M i j‖₊) : NNReal) : ℝ) := hcast
  linarith

/-- **Stone 3a: the trace-vs-diagonal pairing bound.** N-free: only the
diagonal mass Σ d appears, never the dimension. -/
theorem abs_trace_diagonal_mul_le
    (d : Fin N → ℝ) (hd : ∀ m, 0 ≤ d m)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    |Matrix.trace (Matrix.diagonal d * M)| ≤ (∑ m : Fin N, d m) * ‖M‖ := by
  have htr : Matrix.trace (Matrix.diagonal d * M) = ∑ m : Fin N, d m * M m m := by
    unfold Matrix.trace
    congr 1
    funext m
    simp [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Finset.sum_ite_eq, Finset.mem_univ]
  rw [htr]
  calc
    |∑ m : Fin N, d m * M m m|
        ≤ ∑ m : Fin N, |d m * M m m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin N, d m * ‖M‖ := by
      refine Finset.sum_le_sum (fun m _ => ?_)
      rw [abs_mul, abs_of_nonneg (hd m)]
      exact mul_le_mul_of_nonneg_left
        (abs_diag_entry_le_linfty_norm M m) (hd m)
    _ = (∑ m : Fin N, d m) * ‖M‖ := by
      rw [← Finset.sum_mul]

#print axioms abs_diag_entry_le_linfty_norm
#print axioms abs_trace_diagonal_mul_le

end RHFormalization
