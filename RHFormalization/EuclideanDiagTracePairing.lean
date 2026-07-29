-- SENTINEL: EUCTRACE-v1
import RHFormalization.FreeResolventNormBound
import Mathlib

/-!
# EuclideanDiagTracePairing — stone 3b-i

CONSUMER: the ‖Z‖ remainder bound (Z = Tr(R_D·V·R_H·T)), which is `hr` of
`seam_bdd_of_parts` (SEAMASM) → `h_ctail_le_of_seam_bdd` (B2CONN) → GATE → RH.

  ‖Tr(M ∘ D)‖ ≤ (Σ ‖dᵢ‖) · C    for D diagonal on an ONB with entries dᵢ
                                 and ‖M x‖ ≤ C‖x‖.

N-FREE: the dimension never enters — only the diagonal mass Σ‖dᵢ‖, which for
the free resolvent is the convergent p-series (banked `summable_inv_nsq_add_one`
via `galerkinLam_growth`). Measured: |Z| = 6.4976e-2 → 6.5024e-2 for N = 8→128.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

variable {N : ℕ}

/-- ONB diagonal entry of an operator is bounded by its operator bound. -/
theorem norm_onb_diag_entry_le
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (M : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (C : ℝ) (hM : ∀ x : EuclideanSpace ℂ (Fin N), ‖M x‖ ≤ C * ‖x‖)
    (i : Fin N) :
    ‖b.repr (M (b i)) i‖ ≤ C := by
  have hb1 : ‖b i‖ = 1 := b.orthonormal.1 i
  have hinner : b.repr (M (b i)) i = inner ℂ (b i) (M (b i)) :=
    b.repr_apply_apply _ i
  rw [hinner]
  calc ‖inner ℂ (b i) (M (b i))‖
      ≤ ‖b i‖ * ‖M (b i)‖ := norm_inner_le_norm _ _
    _ = ‖M (b i)‖ := by rw [hb1, one_mul]
    _ ≤ C * ‖b i‖ := hM _
    _ = C := by rw [hb1, mul_one]

/-- **Stone 3b-i: Euclidean diagonal-trace pairing.** N-free. -/
theorem norm_trace_mul_diag_le
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (D M : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (d : Fin N → ℂ)
    (hD : ∀ i, D (b i) = d i • b i)
    (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ x : EuclideanSpace ℂ (Fin N), ‖M x‖ ≤ C * ‖x‖) :
    ‖LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (M * D)‖
      ≤ (∑ i, ‖d i‖) * C := by
  classical
  have hbi : ∀ i : Fin N, b.toBasis i = b i := by
    intro i
    first
      | rw [OrthonormalBasis.coe_toBasis]
      | simp [OrthonormalBasis.coe_toBasis]
      | rfl
  have hreprb : ∀ (y : EuclideanSpace ℂ (Fin N)) (i : Fin N),
      b.toBasis.repr y i = b.repr y i := by
    intro y i
    first
      | rw [OrthonormalBasis.coe_toBasis_repr_apply]
      | simp [OrthonormalBasis.coe_toBasis_repr_apply]
      | rfl
  have hentry : ∀ i : Fin N,
      LinearMap.toMatrix b.toBasis b.toBasis (M * D) i i
        = d i * b.repr (M (b i)) i := by
    intro i
    rw [LinearMap.toMatrix_apply, hbi i]
    have hcomp : (M * D) (b i) = M (d i • b i) := by
      change M (D (b i)) = M (d i • b i)
      rw [hD i]
    rw [hcomp]
    have hstep : b.toBasis.repr (M (d i • b i)) i
        = d i * b.toBasis.repr (M (b i)) i := by
      rw [map_smul, map_smul]
      simp [Finsupp.smul_apply, smul_eq_mul]
    rw [hstep, hreprb]
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  have htr : Matrix.trace (LinearMap.toMatrix b.toBasis b.toBasis (M * D))
      = ∑ i, d i * b.repr (M (b i)) i := by
    unfold Matrix.trace
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply]
    exact hentry i
  rw [htr]
  calc ‖∑ i, d i * b.repr (M (b i)) i‖
      ≤ ∑ i, ‖d i * b.repr (M (b i)) i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖d i‖ * C := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_onb_diag_entry_le b M C hM i) (norm_nonneg _)
    _ = (∑ i, ‖d i‖) * C := by rw [← Finset.sum_mul]

#print axioms norm_onb_diag_entry_le
#print axioms norm_trace_mul_diag_le

end

end RHFormalization
