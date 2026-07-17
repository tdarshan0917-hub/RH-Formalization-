-- SENTINEL: decoded-eigenvalue-floor-v1
import RHFormalization.AdmissibleEigenvalueFloor
import RHFormalization.DecodedGalerkinFStageForwardGate
import Mathlib

/-!
# The DECODED eigenvalue floor
UPSTREAM: decodedPrimePotentialFn_nonneg (banked), gaussBump machinery,
  re_form_complexified (generic), perturbedOp variational kit (generic).
  Donor proofs: AdmissibleWeightNonneg.lean + AdmissibleEigenvalueFloor.lean,
  ported line-for-line with decoded centers — proofs are center-generic
  (integral of potential×trial², potential pointwise nonneg).
TARGET: 0 ≤ perturbedEigenvalues μ (decodedGalerkinVC_isHermitian 1 qs w L) i.
DOWNSTREAM CONSUMER: decodedShiftedFStage_holo → decoded_selected_F_stage_holo
  → decoded_selected_R_stage_holo → buildDMasterResidualDataAlong.h_stage_holo.
SEMANTIC: fixed-N spectral floor; δ = 1, ppWeightReal, decoded centers.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real
open scoped BigOperators

/-- Continuity of the decoded prime potential (δ ≠ 0). -/
theorem continuous_decodedPrimePotentialFn_gen
    (δ : ℝ) (hδ : δ ≠ 0) (qs : Finset ℕ) :
    Continuous (decodedPrimePotentialFn δ qs ppWeightReal) := by
  unfold decodedPrimePotentialFn
  apply continuous_finsetSum
  intro q _
  unfold gaussBump
  have hden : Real.sqrt (2 * Real.pi * δ ^ 2) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    positivity
  fun_prop

/-- Decoded form = position-space integral on [0, L]. -/
theorem decodedGalerkinV_form_eq_integral_L
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ) (a : Fin N → ℝ) :
    ∑ m : Fin N, ∑ n : Fin N,
        a m * a n * decodedGalerkinV (N := N) 1 qs ppWeightReal L m n
      = (2 / L) * ∫ x in (0:ℝ)..L,
          decodedPrimePotentialFn 1 qs ppWeightReal x
            * (galerkinTrialL L a x) ^ 2 := by
  have hint : ∀ (g : ℝ → ℝ), Continuous g →
      IntervalIntegrable g MeasureTheory.volume 0 L :=
    fun g hg => hg.intervalIntegrable 0 L
  have hexp : ∀ x : ℝ,
      decodedPrimePotentialFn 1 qs ppWeightReal x * (galerkinTrialL L a x) ^ 2
        = ∑ m : Fin N, ∑ n : Fin N,
            a m * a n * (dirichletEigenfun ((m:ℕ)+1) L x
              * decodedPrimePotentialFn 1 qs ppWeightReal x
              * dirichletEigenfun ((n:ℕ)+1) L x) := by
    intro x
    unfold galerkinTrialL
    rw [sq, Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  calc ∑ m : Fin N, ∑ n : Fin N,
        a m * a n * decodedGalerkinV (N := N) 1 qs ppWeightReal L m n
      = (2 / L) * ∑ m : Fin N, ∑ n : Fin N, a m * a n
          * ∫ x in (0:ℝ)..L,
              dirichletEigenfun ((m:ℕ)+1) L x
                * decodedPrimePotentialFn 1 qs ppWeightReal x
                * dirichletEigenfun ((n:ℕ)+1) L x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        show a m * a n *
            ((2 / L) *
              decodedVmatrixElement 1 qs ppWeightReal L ((m:ℕ)+1) ((n:ℕ)+1))
          = _
        first
          | (unfold decodedVmatrixElement; ring)
          | (rw [show decodedVmatrixElement 1 qs ppWeightReal L ((m:ℕ)+1) ((n:ℕ)+1)
                = ∫ x in (0:ℝ)..L,
                    dirichletEigenfun ((m:ℕ)+1) L x
                      * decodedPrimePotentialFn 1 qs ppWeightReal x
                      * dirichletEigenfun ((n:ℕ)+1) L x from rfl]
             ring)
    _ = (2 / L) * ∑ m : Fin N, ∑ n : Fin N,
          ∫ x in (0:ℝ)..L, a m * a n
            * (dirichletEigenfun ((m:ℕ)+1) L x
              * decodedPrimePotentialFn 1 qs ppWeightReal x
              * dirichletEigenfun ((n:ℕ)+1) L x) := by
        congr 1
        apply Finset.sum_congr rfl; intro m _
        apply Finset.sum_congr rfl; intro n _
        rw [intervalIntegral.integral_const_mul]
    _ = (2 / L) * ∫ x in (0:ℝ)..L, ∑ m : Fin N, ∑ n : Fin N, a m * a n
          * (dirichletEigenfun ((m:ℕ)+1) L x
            * decodedPrimePotentialFn 1 qs ppWeightReal x
            * dirichletEigenfun ((n:ℕ)+1) L x) := by
        congr 1
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl; intro m _
          rw [intervalIntegral.integral_finsetSum]
          intro n _
          apply hint
          apply Continuous.const_mul
          exact ((continuous_dirichletEigenfun _ L).mul
            (continuous_decodedPrimePotentialFn_gen 1 one_ne_zero qs)).mul
            (continuous_dirichletEigenfun _ L)
        · intro m _
          apply hint
          apply continuous_finsetSum
          intro n _
          apply Continuous.const_mul
          exact ((continuous_dirichletEigenfun _ L).mul
            (continuous_decodedPrimePotentialFn_gen 1 one_ne_zero qs)).mul
            (continuous_dirichletEigenfun _ L)
    _ = (2 / L) * ∫ x in (0:ℝ)..L,
          decodedPrimePotentialFn 1 qs ppWeightReal x
            * (galerkinTrialL L a x) ^ 2 := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x _
        exact (hexp x).symm

/-- Decoded bump form is nonnegative at every window. -/
theorem decodedGalerkinV_form_nonneg_L
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ) (a : Fin N → ℝ) :
    0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        a m * a n * decodedGalerkinV (N := N) 1 qs ppWeightReal L m n := by
  rw [decodedGalerkinV_form_eq_integral_L L hL qs a]
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) L,
      0 ≤ decodedPrimePotentialFn 1 qs ppWeightReal x
        * (galerkinTrialL L a x) ^ 2 :=
    fun x _ => mul_nonneg
      (decodedPrimePotentialFn_nonneg 1 one_pos qs x) (sq_nonneg _)
  refine mul_nonneg (by positivity) ?_
  first
    | exact intervalIntegral.intervalIntegral_nonneg hpt (le_of_lt hL)
    | exact intervalIntegral.integral_nonneg (le_of_lt hL) hpt
    | exact intervalIntegral.integral_nonneg (le_of_lt hL)
        (fun x hx => hpt x hx)
    | (apply intervalIntegral.integral_nonneg (le_of_lt hL)
       intro x hx
       exact hpt x hx)

/-- Complexified decoded form is nonnegative. -/
theorem decodedGalerkinVC_re_form_nonneg_L
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ)
    (y : EuclideanSpace ℂ (Fin N)) :
    0 ≤ RCLike.re (inner ℂ y
        (pertOp (decodedGalerkinVC (N := N) 1 qs ppWeightReal L) y)) := by
  have hVC : decodedGalerkinVC (N := N) 1 qs ppWeightReal L
      = fun i j =>
          ((decodedGalerkinV (N := N) 1 qs ppWeightReal L i j : ℝ) : ℂ) := rfl
  rw [hVC, re_form_complexified]
  have hre' : 0 ≤ ∑ n : Fin N, ∑ m : Fin N,
      (y n).re * decodedGalerkinV (N := N) 1 qs ppWeightReal L n m * (y m).re := by
    have heq : ∑ n : Fin N, ∑ m : Fin N,
        (y n).re * decodedGalerkinV (N := N) 1 qs ppWeightReal L n m * (y m).re
        = ∑ n : Fin N, ∑ m : Fin N,
            (y n).re * (y m).re * decodedGalerkinV (N := N) 1 qs ppWeightReal L n m := by
      apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro m _
      ring
    rw [heq]
    exact decodedGalerkinV_form_nonneg_L L hL qs (fun k => (y k).re)
  have him' : 0 ≤ ∑ n : Fin N, ∑ m : Fin N,
      (y n).im * decodedGalerkinV (N := N) 1 qs ppWeightReal L n m * (y m).im := by
    have heq : ∑ n : Fin N, ∑ m : Fin N,
        (y n).im * decodedGalerkinV (N := N) 1 qs ppWeightReal L n m * (y m).im
        = ∑ n : Fin N, ∑ m : Fin N,
            (y n).im * (y m).im * decodedGalerkinV (N := N) 1 qs ppWeightReal L n m := by
      apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro m _
      ring
    rw [heq]
    exact decodedGalerkinV_form_nonneg_L L hL qs (fun k => (y k).im)
  exact add_nonneg hre' him'

/-- **THE DECODED EIGENVALUE FLOOR (unshifted).** Nonneg free spectrum +
nonneg decoded bump form ⟹ every decoded eigenvalue is nonnegative. -/
theorem decodedEigenvalue_nonneg
    {N : ℕ} (L : ℝ) (hL : 0 < L) (qs : Finset ℕ) (μ : Fin N → ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (i : Fin N) :
    0 ≤ perturbedEigenvalues μ
          (decodedGalerkinVC_isHermitian (N := N) 1 qs ppWeightReal L) i := by
  set hV : (decodedGalerkinVC (N := N) 1 qs ppWeightReal L).IsHermitian :=
    decodedGalerkinVC_isHermitian (N := N) 1 qs ppWeightReal L with hVdef
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
      perturbedOp μ (decodedGalerkinVC (N := N) 1 qs ppWeightReal L) v
        = (perturbedEigenvalues μ hV i : ℂ) • v := by
    have h :=
      (perturbedOp_isSymmetric μ hV).hasEigenvector_eigenvectorBasis
        perturbedOp_finrank i
    first
      | exact h.apply_eq_smul
      | simpa [perturbedEigenvalues, hvdef] using h.apply_eq_smul
  have hform :
      RCLike.re (inner ℂ v
          (perturbedOp μ (decodedGalerkinVC (N := N) 1 qs ppWeightReal L) v))
        = perturbedEigenvalues μ hV i := by
    rw [hev, inner_smul_right, hvv, mul_one]
    first
      | exact RCLike.ofReal_re _
      | exact Complex.ofReal_re _
      | simp
  have happ2 : perturbedOp μ (decodedGalerkinVC (N := N) 1 qs ppWeightReal L) v
      = freeDiagOp μ v + pertOp (decodedGalerkinVC (N := N) 1 qs ppWeightReal L) v := by
    rw [perturbedOp_eq_add]
    first
      | exact LinearMap.add_apply _ _ _
      | rfl
      | simp
  have hsplit :
      RCLike.re (inner ℂ v
          (perturbedOp μ (decodedGalerkinVC (N := N) 1 qs ppWeightReal L) v))
        = RCLike.re (inner ℂ v (freeDiagOp μ v))
          + RCLike.re (inner ℂ v
              (pertOp (decodedGalerkinVC (N := N) 1 qs ppWeightReal L) v)) := by
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
  have hpert := decodedGalerkinVC_re_form_nonneg_L (N := N) L hL qs v
  have h0 : 0 ≤ RCLike.re (inner ℂ v
      (perturbedOp μ (decodedGalerkinVC (N := N) 1 qs ppWeightReal L) v)) := by
    rw [hsplit]
    exact add_nonneg hfree hpert
  rw [← hform]
  exact h0

#print axioms continuous_decodedPrimePotentialFn_gen
#print axioms decodedGalerkinV_form_eq_integral_L
#print axioms decodedGalerkinV_form_nonneg_L
#print axioms decodedGalerkinVC_re_form_nonneg_L
#print axioms decodedEigenvalue_nonneg

end

end RHFormalization
