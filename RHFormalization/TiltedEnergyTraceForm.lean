-- SENTINEL: E3-tilted-energy-trace-form-v2
import RHFormalization.TiltedEnergyDefinitions
import Mathlib

/-!
# E3 — Trace representation of the tilted energy
`tiltedEnergy = (1/2L)·Tr[C.transpose · diag((λ_k+a)⁻¹) · C]`.
The diagonal matrix of reciprocals IS the resolvent (galerkinK diagonal);
no Matrix.inv. v2: `ᵀ` token not parsed under pin → `.transpose`; proof via
generic sandwich helper (pure sum rearrangement, entries opaque).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- **Generic diagonal sandwich trace**: for any real matrix `C` and diagonal
weights `d`, `Tr(Cᵀ·diag(d)·C) = Σ_k d k · Σ_j C(k,j)²`. -/
theorem trace_transpose_diag_sandwich (d : Fin N → ℝ)
    (C : Matrix (Fin N) (Fin N) ℝ) :
    (C.transpose * Matrix.diagonal d * C).trace
      = ∑ k : Fin N, d k * ∑ j : Fin N, (C k j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **E3 — the trace form**: the basis-sum energy equals the trace of the
diagonal-resolvent sandwich, density-normalized. -/
theorem tiltedEnergy_eq_trace_resolvent
    (qs : Finset ℕ) (w : ℕ → ℝ) (L R η a : ℝ) :
    tiltedEnergy (N := N) qs w L R η a
      = (1 / (2 * L)) *
        ((tiltedCenteredMatrix (N := N) qs w L R η).transpose
          * Matrix.diagonal (fun k : Fin N => 1 / (galerkinLam L (k : ℕ) + a))
          * tiltedCenteredMatrix (N := N) qs w L R η).trace := by
  rw [trace_transpose_diag_sandwich]
  unfold tiltedEnergy tiltedCenteredMatrix
  rfl

#print axioms trace_transpose_diag_sandwich
#print axioms tiltedEnergy_eq_trace_resolvent

end

end RHFormalization
