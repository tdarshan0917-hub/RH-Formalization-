-- SENTINEL: HSTRACE-v1
import RHFormalization.SymmetricRayleighOpBound
import Mathlib

/-!
# HilbertSchmidtTraceBound — the sharp replacement for the mass step

CONSUMER: the Z estimate feeding `hr` of `seam_bdd_of_parts` → GATE → RH.

  ‖Tr(A·B)‖ ≤ ‖A‖_HS · ‖B‖_HS

The diagonal-mass version (banked EUCTRACE) costs Σ|s+μᵢ|⁻¹ ~ L²/6, which the
1/(2L) density factor cannot absorb. The HS version costs (Σ|s+μᵢ|⁻²)^{1/2} ~ √L,
which it can. Measured target: |Z|/(2L) peaks at L=8 then decays (ratios
1.865 → 0.642 → 0.495).

Pure Cauchy–Schwarz over the index pair — no dimension factor.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

variable {N : ℕ}

/-- Hilbert–Schmidt norm of a finite complex matrix. -/
def hsNorm (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (∑ p : Fin N × Fin N, ‖A p.1 p.2‖ ^ 2)

theorem hsNorm_nonneg (A : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ hsNorm A :=
  Real.sqrt_nonneg _

/-- **The Hilbert–Schmidt trace bound.** -/
theorem abs_trace_mul_le_hs (A B : Matrix (Fin N) (Fin N) ℂ) :
    ‖Matrix.trace (A * B)‖ ≤ hsNorm A * hsNorm B := by
  classical
  have htr : Matrix.trace (A * B)
      = ∑ p : Fin N × Fin N, A p.1 p.2 * B p.2 p.1 := by
    rw [Fintype.sum_prod_type]
    unfold Matrix.trace
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
  have h1 : ‖∑ p : Fin N × Fin N, A p.1 p.2 * B p.2 p.1‖
      ≤ ∑ p : Fin N × Fin N, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum (fun p _ => le_of_eq (norm_mul _ _))
  have hcs : (∑ p : Fin N × Fin N, ‖A p.1 p.2‖ * ‖B p.2 p.1‖) ^ 2
      ≤ (∑ p : Fin N × Fin N, ‖A p.1 p.2‖ ^ 2)
        * (∑ p : Fin N × Fin N, ‖B p.2 p.1‖ ^ 2) := by
    first
      | exact Finset.inner_mul_le_norm_mul_norm _ _ _
      | exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      | exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      | exact Finset.sum_sqrt_mul_sqrt_le _ _ _
  have hswap : (∑ p : Fin N × Fin N, ‖B p.2 p.1‖ ^ 2)
      = ∑ p : Fin N × Fin N, ‖B p.1 p.2‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.prodComm (Fin N) (Fin N))
      (fun p => ‖B p.2 p.1‖ ^ 2) (fun q => ‖B q.1 q.2‖ ^ 2) (fun p => rfl)
  have ha : (0:ℝ) ≤ ∑ p : Fin N × Fin N, ‖A p.1 p.2‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hS : (0:ℝ) ≤ ∑ p : Fin N × Fin N, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hS2 : (∑ p : Fin N × Fin N, ‖A p.1 p.2‖ * ‖B p.2 p.1‖) ^ 2
      ≤ (∑ p : Fin N × Fin N, ‖A p.1 p.2‖ ^ 2)
        * (∑ p : Fin N × Fin N, ‖B p.1 p.2‖ ^ 2) := by
    rw [← hswap]
    exact hcs
  have hfin : (∑ p : Fin N × Fin N, ‖A p.1 p.2‖ * ‖B p.2 p.1‖)
      ≤ hsNorm A * hsNorm B := by
    have h := Real.sqrt_le_sqrt hS2
    rw [Real.sqrt_sq hS, Real.sqrt_mul ha] at h
    exact h
  rw [htr]
  exact le_trans h1 hfin

#print axioms hsNorm_nonneg
#print axioms abs_trace_mul_le_hs

end

end RHFormalization
