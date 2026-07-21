import RHFormalization.SpikeTransferAtStage
import RHFormalization.RealSpectralTraceBridge
import RHFormalization.AdmissiblePrimeStageIdentity
import Mathlib

/-!
# PrimeHeatIntegrandM2 — T1: the prime heat integrand in M2 coordinates

ROUTE CARD
1. Target: at stage n, the REAL prime heat-trace difference
   `Σ e^{−t·λᵢ^pert} − Σ e^{−t·λᵢ^free}` equals `−t·(diag V term) + E₂(t)`.
   Pointwise in t, unconditional, live net. Free trace via diagonal
   computation: galerkinK = Matrix.diagonal(galerkinLam entries).
2. Bridges (banked): trace_exp_neg_KV_eq_eigen_sum,
   spikeTransfer_M2_form_at_stage. Wrong-kernel fence respected.
3. Raw B on Ω? NO. hstar-equivalent hypothesis? NONE — identity.
4. Consumer: T2 (diagonal-vs-spike matching), T3 (E₂ tail integral)
   → DBFFO3ParabolaDepthHstar.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Free heat trace = free eigensum: direct diagonal computation. -/
theorem trace_exp_neg_K_eq_free_eigen_sum (n : ℕ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := admN n) (admL n))))).trace
      = ∑ i : Fin (admN n),
          Real.exp (-t * galerkinLam (admL n) (i : ℕ)) := by
  have hdiag : t • (-(galerkinK (N := admN n) (admL n)))
      = Matrix.diagonal (fun m : Fin (admN n) =>
          t * (-((((m : ℝ) + 1) * Real.pi / (admL n)) ^ 2))) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [galerkinK, Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Matrix.neg_apply, smul_eq_mul]
    · simp [galerkinK, Matrix.diagonal_apply_ne _ h, Matrix.smul_apply,
        Matrix.neg_apply, h]
  rw [hdiag]
  have hexp : NormedSpace.exp (Matrix.diagonal (fun m : Fin (admN n) =>
      t * (-((((m : ℝ) + 1) * Real.pi / (admL n)) ^ 2))))
      = Matrix.diagonal (fun m : Fin (admN n) =>
          Real.exp (t * (-((((m : ℝ) + 1) * Real.pi / (admL n)) ^ 2)))) := by
    first
      | exact Matrix.exp_diagonal _
      | exact Matrix.exp_diagonal
          (fun m : Fin (admN n) =>
            t * (-((((m : ℝ) + 1) * Real.pi / (admL n)) ^ 2)))
      | exact Matrix.exp_diagonal (m := ℝ) _
      | (have h := Matrix.exp_diagonal
           (fun m : Fin (admN n) =>
             t * (-((((m : ℝ) + 1) * Real.pi / (admL n)) ^ 2)))
         rw [h]
         congr 1
         funext m
         first
           | rw [Pi.exp_apply]
           | simp [Pi.exp_apply]
           | simp [Real.exp_eq_exp_ℝ, Pi.exp_apply]
           | simp [Real.exp_eq_exp_ℝ]
           | rfl)
  rw [hexp, Matrix.trace_diagonal]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  unfold galerkinLam
  ring

/-- **T1: THE PRIME HEAT DIFFERENCE IN M2 COORDINATES** (pointwise in t,
stage n, live net, unconditional). -/
theorem primeHeatDiff_eq_M2 (n : ℕ) (t : ℝ) :
    (∑ i : Fin (admN n),
        Real.exp (-t * admPerturbedLam n i))
      - (∑ i : Fin (admN n),
          Real.exp (-t * galerkinLam (admL n) (i : ℕ)))
      = - t * (∑ m : Fin (admN n),
            galerkinV (N := admN n) 1
              (activePrimePowerCodesCenterBelow (admR n))
              ppWeightReal (admL n) m m
            * Real.exp (-(t * galerkinLam (admL n) (m : ℕ))))
        + spikeTransferE2 (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n))
            ppWeightReal (admL n) t := by
  have hpert : (∑ i : Fin (admN n), Real.exp (-t * admPerturbedLam n i))
      = (NormedSpace.exp (t • (-(galerkinK (N := admN n) (admL n)
          + galerkinV (N := admN n) 1
              (activePrimePowerCodesCenterBelow (admR n))
              ppWeightReal (admL n))))).trace := by
    rw [trace_exp_neg_KV_eq_eigen_sum]
    rfl
  have hfree := trace_exp_neg_K_eq_free_eigen_sum n t
  have hM2 := spikeTransfer_M2_form_at_stage n t
  rw [hpert, ← hfree, hM2]
  ring

#print axioms trace_exp_neg_K_eq_free_eigen_sum
#print axioms primeHeatDiff_eq_M2

end

end RHFormalization
