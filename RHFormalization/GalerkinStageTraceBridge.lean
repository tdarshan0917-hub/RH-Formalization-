/-
GalerkinStageTraceBridge.lean

INDEXING BRIDGE for Front F's convergence: the stage-n SHIFTED F-slot is
the finite sum over smallest-first index k of resolvent terms at
diagLamAt k (n-1-k) + SupVConst. Pure bookkeeping (Fin.rev bijection +
dimension arithmetic); the analysis file consumes this clean statement.
-/
import RHFormalization.GalerkinDiagLimit
import RHFormalization.GalerkinEigenvalueFloor

namespace RHFormalization

noncomputable section

open Complex

/-- Helper over an abstract dimension: when D = n+1 and C = n, the
D-dimensional eigenvalue at rev k equals the stage-n one. Substitution is
legal because D and C are variables. -/
theorem stage_eig_eq_of_dim (n k D C : ℕ) (hD : D = n + 1) (hC : C = n)
    (hkD : k < D) (hkn : k < n + 1) :
    perturbedEigenvalues (galerkinFreeMu D 1)
      (galerkinVC_isHermitian (N := D) 1 (stageCodes C) ppWeightReal 1)
      (Fin.rev (⟨k, hkD⟩ : Fin D))
    = perturbedEigenvalues (galerkinFreeMu (n + 1) 1)
        (galerkinVC_isHermitian (N := n + 1) 1 (stageCodes n) ppWeightReal 1)
        (Fin.rev (⟨k, hkn⟩ : Fin (n + 1))) := by
  subst hD
  subst hC
  rfl

theorem stage_eig_eq_diagLamAt (n k : ℕ) (hk : k < n) :
    perturbedEigenvalues (galerkinFreeMu (n + 1) 1)
      (galerkinVC_isHermitian (N := n + 1) 1 (stageCodes n) ppWeightReal 1)
      (Fin.rev (⟨k, by omega⟩ : Fin (n + 1)))
    = diagLamAt k (n - 1 - k) := by
  unfold diagLamAt
  exact (stage_eig_eq_of_dim n k (k + 2 + (n - 1 - k)) (k + 1 + (n - 1 - k))
    (by omega) (by omega) (by omega) (by omega)).symm

/-- **THE STAGE TRACE, RE-ENUMERATED**: the stage-n shifted F-slot as the
sum over k in range (n+1) of resolvent terms at the diagonal spectrum,
with the top index k = n written via its own defining eigenvalue. For the
convergence proof only the k < n terms matter en masse; the k = n term is
a single vanishing term handled by the uniform tail bound, so we state
the clean version: the full sum over sorted indices transported through
rev. -/
theorem stage_shifted_trace_eq (n : ℕ) (s : ℂ) :
    galerkinPerturbedFStage (N := n + 1) (galerkinFreeMu (n + 1) 1) 1
        (stageCodes n) ppWeightReal 1 (s + (SupVConst : ℂ))
    = ∑ k : Fin (n + 1),
        (s + ((perturbedEigenvalues (galerkinFreeMu (n + 1) 1)
          (galerkinVC_isHermitian (N := n + 1) 1 (stageCodes n) ppWeightReal 1)
          (Fin.rev k) + SupVConst : ℝ) : ℂ))⁻¹ := by
  unfold galerkinPerturbedFStage
  rw [perturbedFStage_shift_eq]
  unfold FstageFinite
  refine (Fintype.sum_bijective Fin.rev ?_ _ _ ?_).symm
  · first
      | exact Fin.rev_bijective
      | exact Function.Involutive.bijective Fin.rev_involutive
      | exact ⟨Fin.rev_injective, Fin.rev_surjective⟩
  · intro k
    rfl

/-- The k < n summands, identified with the diagonal family. -/
theorem stage_shifted_term_eq (n k : ℕ) (hk : k < n) (s : ℂ) :
    (s + ((perturbedEigenvalues (galerkinFreeMu (n + 1) 1)
        (galerkinVC_isHermitian (N := n + 1) 1 (stageCodes n) ppWeightReal 1)
        (Fin.rev (⟨k, by omega⟩ : Fin (n + 1))) + SupVConst : ℝ) : ℂ))⁻¹
    = (s + ((diagLamAt k (n - 1 - k) + SupVConst : ℝ) : ℂ))⁻¹ := by
  rw [stage_eig_eq_diagLamAt n k hk]

/-- Uniform floor at every stage and every sorted index, in the shifted
smallest-first form the tail bound consumes: the k-th smallest shifted
eigenvalue at stage n dominates pi^2 (k+1)^2 - ... shifted: >= pi^2(k+1)^2
- SupVConst + SupVConst >= ... we record the shifted floor >= pi^2 k^2. -/
theorem stage_shifted_eig_floor (n : ℕ) (k : Fin (n + 1)) :
    Real.pi ^ 2 * (((k : ℕ) : ℝ)) ^ 2
      ≤ perturbedEigenvalues (galerkinFreeMu (n + 1) 1)
          (galerkinVC_isHermitian (N := n + 1) 1 (stageCodes n) ppWeightReal 1)
          (Fin.rev k) + SupVConst := by
  have h := galerkinEigenvalue_ge_pi_sq (N := n + 1) (stageCodes n) (Fin.rev k)
  have hrevrev : ((Fin.rev (Fin.rev k)) : ℕ) = (k : ℕ) := by
    first
      | (rw [Fin.rev_rev])
      | (rw [Fin.val_rev, Fin.val_rev]; omega)
      | simp
  rw [hrevrev] at h
  have hsq : Real.pi ^ 2 * (((k : ℕ) : ℝ)) ^ 2
      ≤ Real.pi ^ 2 * (((k : ℕ) : ℝ) + 1) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Real.pi)
    have : (0:ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  linarith

#print axioms stage_eig_eq_diagLamAt
#print axioms stage_shifted_trace_eq
#print axioms stage_shifted_term_eq
#print axioms stage_shifted_eig_floor

end

end RHFormalization
