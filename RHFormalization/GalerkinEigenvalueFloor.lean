/-
GalerkinEigenvalueFloor.lean

THE EIGENVALUE FLOOR (A/B.UNIFORM-LOWER-BOUND, spectral form): every
eigenvalue of the genuine galerkin operator H_N = D + V_pp satisfies
0 <= lambda_i + SupVConst, by Rayleigh evaluation of the banked uniform
form bound at each spectral-theorem eigenvector.

Consequences: the SHIFTED stage resolvent trace s -> F_stage(s + SupVConst)
equals the finite resolvent trace of the shifted spectrum, hence is
holomorphic on Omega at EVERY stage -- the per-stage holomorphy input for
Front F (DFHLimitData) and Front R (DMasterResidualData).
-/
import RHFormalization.GalerkinUniformShift
import RHFormalization.GalerkinFStageForwardGate
import RHFormalization.GalerkinStagePackage
import RHFormalization.FiniteStageSpectrum
import RHFormalization.PerturbedResidual

namespace RHFormalization

noncomputable section

open Complex

variable {N : ℕ}

/-- **THE EIGENVALUE FLOOR.** Every eigenvalue of the genuine galerkin
operator is at least -SupVConst: Rayleigh evaluation of the banked uniform
form bound at the i-th eigenvector. -/
theorem galerkinEigenvalue_floor
    (qs : Finset ℕ) (μ : Fin N → ℝ) (hμ : ∀ k, 0 ≤ μ k) (i : Fin N) :
    0 ≤ perturbedEigenvalues μ
          (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1) i
        + SupVConst := by
  set hV : (galerkinVC (N := N) 1 qs ppWeightReal 1).IsHermitian :=
    galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1 with hVdef
  set v : EuclideanSpace ℂ (Fin N) :=
    (perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank i with hvdef
  have hON :
      Orthonormal ℂ
        ⇑((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) :=
    ((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank).orthonormal
  have hnorm : ‖v‖ = 1 := hON.norm_eq_one i
  have hvv : inner ℂ v v = (1 : ℂ) := by
    have h := orthonormal_iff_ite.mp hON i i
    rw [if_pos rfl] at h
    first
      | exact h
      | (rw [hvdef]; exact h)
  have hev :
      perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal 1) v
        = (perturbedEigenvalues μ hV i : ℂ) • v := by
    have h :=
      (perturbedOp_isSymmetric μ hV).hasEigenvector_eigenvectorBasis
        perturbedOp_finrank i
    first
      | exact h.apply_eq_smul
      | simpa [perturbedEigenvalues, hvdef] using h.apply_eq_smul
  have hform :
      RCLike.re (inner ℂ v
          (perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal 1) v))
        = perturbedEigenvalues μ hV i := by
    rw [hev, inner_smul_right, hvv, mul_one]
    first
      | exact RCLike.ofReal_re _
      | exact Complex.ofReal_re _
      | simp
  have h0 := galerkinOpCLM_nonneg_uniform (N := N) qs μ hμ v
  rw [galerkinOpCLM_form_split, hform, hnorm] at h0
  rw [one_pow, mul_one] at h0
  exact h0

/-- Shifting the argument of the finite resolvent trace by M is the same as
shifting every eigenvalue by M. -/
theorem perturbedFStage_shift_eq
    (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (M : ℝ) (s : ℂ) :
    perturbedFStage μ hV (s + (M : ℂ))
      = FstageFinite (fun i => perturbedEigenvalues μ hV i + M) s := by
  unfold perturbedFStage FstageFinite
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  push_cast
  ring

/-- **Per-stage Omega-holomorphy of the SHIFTED genuine F-stage.** -/
theorem galerkinShiftedFStage_holo
    (qs : Finset ℕ) (μ : Fin N → ℝ) (hμ : ∀ k, 0 ≤ μ k) :
    HolomorphicOnC
      (fun s =>
        galerkinPerturbedFStage (N := N) μ 1 qs ppWeightReal 1
          (s + (SupVConst : ℂ))) Ω := by
  have heq :
      (fun s =>
          galerkinPerturbedFStage (N := N) μ 1 qs ppWeightReal 1
            (s + (SupVConst : ℂ)))
        = FstageFinite (fun i =>
            perturbedEigenvalues μ
              (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1) i
              + SupVConst) := by
    funext s
    exact perturbedFStage_shift_eq μ
      (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1) SupVConst s
  rw [heq]
  exact FstageFinite_holo_on_Omega _ (galerkinEigenvalue_floor qs μ hμ)

/-- **Per-stage Omega-holomorphy of the package F-slot** along the genuine
exhaustion: the manuscript-faithful SHIFTED resolvent trace is holomorphic on
Omega at every stage. -/
theorem galerkinStagePackage_F_stage_holo (n : ℕ) :
    HolomorphicOnC
      (fun s => galerkinStagePackage.F_stage (galerkinStageSeq n) s) Ω := by
  have h :=
    galerkinShiftedFStage_holo
      (activePrimePowerCodesCenterBelow ((n : ℝ) + 1))
      (galerkinFreeMu (n + 1) 1)
      (fun k => galerkinFreeMu_nonneg _ _ k)
  first
    | exact h
    | simpa [galerkinStagePackage] using h

#print axioms galerkinEigenvalue_floor
#print axioms perturbedFStage_shift_eq
#print axioms galerkinShiftedFStage_holo
#print axioms galerkinStagePackage_F_stage_holo

end

end RHFormalization
