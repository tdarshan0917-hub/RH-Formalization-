import RHFormalization.AdmissibleWeightNonneg
import RHFormalization.AdmissibleGalerkinStage
import RHFormalization.GalerkinUniformShift
import RHFormalization.GalerkinOpNonnegDischarge
import RHFormalization.GalerkinEigenvalueFloor

/-!
# RHFormalization.AdmissibleEigenvalueFloor

**Brick 3 of the admissible F-front.** With the nonneg frozen weights, the
Galerkin bump form is nonneg at EVERY window (Brick 2), so the admissible
eigenvalues are nonnegative UNSHIFTED: no SupV machinery. Per-stage
Omega-holomorphy of the admissible package F-slot follows.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Real Matrix

/-- Complexified form nonnegativity at every window: real + imag parts. -/
theorem galerkinVC_re_form_nonneg_L
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ)
    (y : EuclideanSpace ℂ (Fin N)) :
    0 ≤ RCLike.re (inner ℂ y
        (pertOp (galerkinVC (N := N) 1 qs ppWeightReal L) y)) := by
  have hVC : galerkinVC (N := N) 1 qs ppWeightReal L
      = fun i j => ((galerkinV (N := N) 1 qs ppWeightReal L i j : ℝ) : ℂ) := rfl
  rw [hVC, re_form_complexified]
  have hre' : 0 ≤ ∑ n : Fin N, ∑ m : Fin N,
      (y n).re * galerkinV (N := N) 1 qs ppWeightReal L n m * (y m).re := by
    have heq : ∑ n : Fin N, ∑ m : Fin N,
        (y n).re * galerkinV (N := N) 1 qs ppWeightReal L n m * (y m).re
        = ∑ n : Fin N, ∑ m : Fin N,
            (y n).re * (y m).re * galerkinV (N := N) 1 qs ppWeightReal L n m := by
      apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro m _
      ring
    rw [heq]
    exact galerkinV_form_nonneg_L L hL qs (fun k => (y k).re)
  have him' : 0 ≤ ∑ n : Fin N, ∑ m : Fin N,
      (y n).im * galerkinV (N := N) 1 qs ppWeightReal L n m * (y m).im := by
    have heq : ∑ n : Fin N, ∑ m : Fin N,
        (y n).im * galerkinV (N := N) 1 qs ppWeightReal L n m * (y m).im
        = ∑ n : Fin N, ∑ m : Fin N,
            (y n).im * (y m).im * galerkinV (N := N) 1 qs ppWeightReal L n m := by
      apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro m _
      ring
    rw [heq]
    exact galerkinV_form_nonneg_L L hL qs (fun k => (y k).im)
  exact add_nonneg hre' him'

/-- **THE ADMISSIBLE EIGENVALUE FLOOR (unshifted).** Nonneg free spectrum +
nonneg bump form ⟹ every admissible eigenvalue is nonnegative. -/
theorem admissibleEigenvalue_nonneg
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ) (μ : Fin N → ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (i : Fin N) :
    0 ≤ perturbedEigenvalues μ
          (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal L) i := by
  set hV : (galerkinVC (N := N) 1 qs ppWeightReal L).IsHermitian :=
    galerkinVC_isHermitian (N := N) 1 qs ppWeightReal L with hVdef
  set v : EuclideanSpace ℂ (Fin N) :=
    (perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank i with hvdef
  have hON :
      Orthonormal ℂ
        ⇑((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) :=
    ((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank).orthonormal
  have hvv : inner ℂ v v = (1 : ℂ) := by
    have h := orthonormal_iff_ite.mp hON i i
    rw [if_pos rfl] at h
    first
      | exact h
      | (rw [hvdef]; exact h)
  have hev :
      perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal L) v
        = (perturbedEigenvalues μ hV i : ℂ) • v := by
    have h :=
      (perturbedOp_isSymmetric μ hV).hasEigenvector_eigenvectorBasis
        perturbedOp_finrank i
    first
      | exact h.apply_eq_smul
      | simpa [perturbedEigenvalues, hvdef] using h.apply_eq_smul
  have hform :
      RCLike.re (inner ℂ v
          (perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal L) v))
        = perturbedEigenvalues μ hV i := by
    rw [hev, inner_smul_right, hvv, mul_one]
    first
      | exact RCLike.ofReal_re _
      | exact Complex.ofReal_re _
      | simp
  have happ2 : perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal L) v
      = freeDiagOp μ v + pertOp (galerkinVC (N := N) 1 qs ppWeightReal L) v := by
    rw [perturbedOp_eq_add]
    first
      | exact LinearMap.add_apply _ _ _
      | rfl
      | simp
  have hsplit :
      RCLike.re (inner ℂ v
          (perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal L) v))
        = RCLike.re (inner ℂ v (freeDiagOp μ v))
          + RCLike.re (inner ℂ v
              (pertOp (galerkinVC (N := N) 1 qs ppWeightReal L) v)) := by
    rw [happ2, inner_add_right, map_add]
  have hfree : 0 ≤ RCLike.re (inner ℂ v (freeDiagOp μ v)) := by
    rw [freeDiagOp_form_eq_sum]
    apply Finset.sum_nonneg
    intro k _
    first
      | exact mul_nonneg (hμ k) (sq_nonneg _)
      | exact mul_nonneg (hμ k) (Complex.normSq_nonneg _)
      | exact mul_nonneg (hμ k) (by positivity)
      | positivity
  have hpert := galerkinVC_re_form_nonneg_L (N := N) L hL qs v
  have h0 : 0 ≤ RCLike.re (inner ℂ v
      (perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal L) v)) := by
    rw [hsplit]
    exact add_nonneg hfree hpert
  rw [← hform]
  exact h0

/-- SupVConst is nonnegative (tsum of nonneg terms). -/
theorem SupVConst_nonneg_adm : 0 ≤ SupVConst := by
  unfold SupVConst
  exact tsum_nonneg (fun k =>
    mul_nonneg (abs_nonneg _) (bumpEnvelope_nonneg k))

/-- Per-stage Omega-holomorphy of the SHIFTED admissible F-trace: the shift
only moves an already-nonneg spectrum further right. -/
theorem admissibleShiftedFStage_holo
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ) (μ : Fin N → ℝ)
    (hμ : ∀ k, 0 ≤ μ k) :
    HolomorphicOnC
      (fun s =>
        galerkinPerturbedFStage (N := N) μ 1 qs ppWeightReal L
          (s + (SupVConst : ℂ))) Ω := by
  have heq :
      (fun s =>
          galerkinPerturbedFStage (N := N) μ 1 qs ppWeightReal L
            (s + (SupVConst : ℂ)))
        = FstageFinite (fun i =>
            perturbedEigenvalues μ
              (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal L) i
              + SupVConst) := by
    funext s
    exact perturbedFStage_shift_eq μ
      (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal L) SupVConst s
  rw [heq]
  refine FstageFinite_holo_on_Omega _ (fun i => ?_)
  have h1 := admissibleEigenvalue_nonneg L hL qs μ hμ i
  have h2 := SupVConst_nonneg_adm
  linarith

/-- **h_stage_holo, F-side, ADMISSIBLE NET**: the package F-slot at every
admissible stage is holomorphic on Ω. -/
theorem galerkinStagePackage_F_stage_holo_admissible (n : ℕ) :
    HolomorphicOnC
      (fun s =>
        galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s) Ω := by
  have hμnn : ∀ k, 0 ≤ galerkinFreeMu (admN n) (admL n) k := by
    intro k
    first
      | exact galerkinFreeMu_nonneg _ _ k
      | (unfold galerkinFreeMu; positivity)
      | exact sq_nonneg _
  have h := admissibleShiftedFStage_holo (admL n) (admL_pos n)
    (activePrimePowerCodesCenterBelow (admR n))
    (galerkinFreeMu (admN n) (admL n)) hμnn
  have heq : (fun s =>
      galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s)
      = fun s => admDensityC n *
          galerkinPerturbedFStage (N := admN n)
            (galerkinFreeMu (admN n) (admL n)) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (admL n) (s + (SupVConst : ℂ)) := by
    funext s
    exact galerkinStagePackage_F_at_admissible n s
  rw [heq]
  first
    | exact analyticOn_const.mul h
    | exact (show AnalyticOn ℂ (fun _ : ℂ => admDensityC n) Ω from
        analyticOn_const).mul h
    | exact h.const_mul (admDensityC n)
    | exact AnalyticOn.mul analyticOn_const h

#print axioms galerkinVC_re_form_nonneg_L
#print axioms admissibleEigenvalue_nonneg
#print axioms SupVConst_nonneg_adm
#print axioms admissibleShiftedFStage_holo
#print axioms galerkinStagePackage_F_stage_holo_admissible

end

end RHFormalization
