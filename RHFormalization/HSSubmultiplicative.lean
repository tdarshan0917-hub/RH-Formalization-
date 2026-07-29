-- SENTINEL: HSSUB-v3
import RHFormalization.FreeResolventHSMass
import Mathlib

/-!
# HSSubmultiplicative — HS × operator submultiplicativity

CONSUMER: the sharpened Z estimate (‖Z‖ ≤ ‖R_D‖_HS·CV·‖R_H‖_HS·CT), whose
consumer is `hr` of `seam_bdd_of_parts` → `h_ctail_le_of_seam_bdd` → GATE → RH.

  ‖B * C‖_HS ≤ K · ‖B‖_HS      when row-vectors satisfy ‖v ᵥ* C‖ ≤ K‖v‖

Row i of (B*C) is (row i of B) acted on by C, so the bound applies rowwise and
sums. L-counting: ‖R_D‖_HS ~ √L (banked HSMASS) and V, T enter only through
operator norms (measured: CV saturates at 10.08, CT = 1.0000), so the product
is ~L and the 1/(2L) density factor absorbs it.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- Row-wise reformulation of the HS norm. -/
theorem hsNorm_sq_eq_row_sums (A : Matrix (Fin N) (Fin N) ℂ) :
    (∑ p : Fin N × Fin N, ‖A p.1 p.2‖ ^ 2)
      = ∑ i : Fin N, ∑ j : Fin N, ‖A i j‖ ^ 2 := by
  rw [Fintype.sum_prod_type]

/-- **HS × operator submultiplicativity** (row form). -/
theorem hsNorm_mul_le
    (B C : Matrix (Fin N) (Fin N) ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hrow : ∀ v : Fin N → ℂ,
      (∑ i : Fin N, ‖∑ j : Fin N, v j * C j i‖ ^ 2)
        ≤ K ^ 2 * ∑ j : Fin N, ‖v j‖ ^ 2) :
    hsNorm (B * C) ≤ K * hsNorm B := by
  classical
  have hrows : (∑ p : Fin N × Fin N, ‖(B * C) p.1 p.2‖ ^ 2)
      ≤ K ^ 2 * ∑ p : Fin N × Fin N, ‖B p.1 p.2‖ ^ 2 := by
    rw [hsNorm_sq_eq_row_sums, hsNorm_sq_eq_row_sums, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hentry : ∀ k : Fin N, (B * C) i k = ∑ j : Fin N, B i j * C j k := by
      intro k; rw [Matrix.mul_apply]
    calc (∑ k : Fin N, ‖(B * C) i k‖ ^ 2)
        = ∑ k : Fin N, ‖∑ j : Fin N, B i j * C j k‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [hentry k]
      _ ≤ K ^ 2 * ∑ j : Fin N, ‖B i j‖ ^ 2 := hrow (fun j => B i j)
  have hBnn : (0:ℝ) ≤ ∑ p : Fin N × Fin N, ‖B p.1 p.2‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => sq_nonneg _)
  unfold hsNorm
  calc Real.sqrt (∑ p : Fin N × Fin N, ‖(B * C) p.1 p.2‖ ^ 2)
      ≤ Real.sqrt (K ^ 2 * ∑ p : Fin N × Fin N, ‖B p.1 p.2‖ ^ 2) :=
        Real.sqrt_le_sqrt hrows
    _ = K * Real.sqrt (∑ p : Fin N × Fin N, ‖B p.1 p.2‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]

/-- Triangle inequality for the HS norm (needed for the second-resolvent step). -/
theorem hsNorm_add_le (A B : Matrix (Fin N) (Fin N) ℂ) :
    hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  classical
  have key : ∀ f g : Fin N × Fin N → ℂ,
      Real.sqrt (∑ p, ‖f p + g p‖ ^ 2)
        ≤ Real.sqrt (∑ p, ‖f p‖ ^ 2) + Real.sqrt (∑ p, ‖g p‖ ^ 2) := by
    intro f g
    have h := norm_add_le
      (show EuclideanSpace ℂ (Fin N × Fin N) from (WithLp.toLp 2 f))
      (show EuclideanSpace ℂ (Fin N × Fin N) from (WithLp.toLp 2 g))
    simpa [EuclideanSpace.norm_eq] using h
  unfold hsNorm
  exact key (fun p => A p.1 p.2) (fun p => B p.1 p.2)

#print axioms hsNorm_mul_le
#print axioms hsNorm_add_le

end

end RHFormalization
