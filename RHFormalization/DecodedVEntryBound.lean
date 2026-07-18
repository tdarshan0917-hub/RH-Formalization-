-- SENTINEL: decoded-v-entry-bound-v1
import RHFormalization.DecodedPrimePotentialBumpSplit
import RHFormalization.AdmissibleColumnNormBound
import Mathlib

/-!
# DecodedVEntryBound — brick 1a of hShort
Entry-level bound for the DECODED potential matrix, center-free mechanism:
|sin·bump·sin| ≤ bump pointwise, window Gaussian mass ≤ full-line mass ≤ 1.
Chain: abs_decodedBumpMatrixElement_le_one → abs_decodedVmatrixElement_le
(≤ S1mass-shaped sum). Feeds the decoded column-norm clone (brick 1b).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real MeasureTheory
open scoped Real BigOperators

/-- Decoded bump mass: window integral of the Gaussian at the PHYSICAL center. -/
def decodedBumpMass (δ : ℝ) (q : ℕ) (L : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..L, gaussBump δ (x - (ppDecode q).center)

theorem intervalIntegrable_gaussBump_decoded (δ : ℝ) (q : ℕ) (L : ℝ) :
    IntervalIntegrable (fun x : ℝ => gaussBump δ (x - (ppDecode q).center))
      MeasureTheory.volume 0 L := by
  first
    | exact (Continuous.intervalIntegrable (by
        unfold gaussBump; fun_prop) 0 L)
    | exact (Continuous.intervalIntegrable (by
        unfold gaussBump; continuity) 0 L)
    | exact ((continuous_gaussBump δ).comp
        (continuous_id.sub continuous_const)).intervalIntegrable 0 L

/-- Window Gaussian mass ≤ 1 at ANY center (δ = 1): the mechanism of
`bumpMass_le_one`, center-free. -/
theorem decodedBumpMass_le_one (q : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    decodedBumpMass 1 q L ≤ 1 := by
  unfold decodedBumpMass
  set a : ℝ := (ppDecode q).center with ha
  have hpos : ∀ x : ℝ, 0 ≤ gaussBump 1 (x - a) := by
    intro x
    unfold gaussBump
    positivity
  have hInt : MeasureTheory.Integrable (fun x : ℝ => gaussBump 1 (x - a)) := by
    unfold gaussBump
    simp only [one_pow, mul_one]
    have h1 : MeasureTheory.Integrable (fun x : ℝ =>
        Real.exp (-(1/2 : ℝ) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
    have h2 : MeasureTheory.Integrable (fun x : ℝ =>
        Real.exp (-(1/2 : ℝ) * (x - a) ^ 2)) := by
      first
        | exact h1.comp_sub_right a
        | exact (MeasureTheory.integrable_comp_sub_right
            (fun x => Real.exp (-(1/2 : ℝ) * x ^ 2)) a).mpr h1
    have h3 : MeasureTheory.Integrable (fun x : ℝ =>
        Real.exp (-(1/2 : ℝ) * (x - a) ^ 2)
          / Real.sqrt (2 * Real.pi)) := by
      first
        | · have h4 := h2.mul_const ((Real.sqrt (2 * Real.pi))⁻¹)
            refine h4.congr ?_
            filter_upwards with x
            rw [div_eq_mul_inv]
        | · have h4 := h2.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
            refine h4.congr ?_
            filter_upwards with x
            rw [div_eq_inv_mul]
        | exact h2.div_const _
    refine h3.congr ?_
    filter_upwards with x
    congr 1
    ring
  have hstep : (∫ x in (0:ℝ)..L, gaussBump 1 (x - a))
      ≤ ∫ x : ℝ, gaussBump 1 (x - a) := by
    rw [intervalIntegral.integral_of_le hL]
    first
      | exact MeasureTheory.setIntegral_le_integral hInt
          (Filter.Eventually.of_forall hpos)
      | exact MeasureTheory.integral_Ioc_le_integral hInt hpos
  refine hstep.trans ?_
  have hshift : (∫ x : ℝ, gaussBump 1 (x - a)) = ∫ u : ℝ, gaussBump 1 u := by
    first
      | exact MeasureTheory.integral_sub_right_eq_self _ a
      | (rw [MeasureTheory.integral_sub_right_eq_self])
  rw [hshift]
  -- full-line mass of the raw bump = window-limit of bumpMass; reuse via q=1, L→∞?
  -- Direct: full-line normalized Gaussian integral ≤ 1 (equality, but ≤ suffices)
  have hfull : (∫ u : ℝ, gaussBump 1 u) ≤ 1 := by
    unfold gaussBump
    simp only [one_pow, mul_one]
    have hg : (∫ x : ℝ, Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))
        = (∫ x : ℝ, Real.exp (-x ^ 2 / 2)) / Real.sqrt (2 * Real.pi) := by
      rw [MeasureTheory.integral_div]
    rw [hg]
    have hrw : (fun x : ℝ => Real.exp (-x ^ 2 / 2))
        = (fun x : ℝ => Real.exp (-(1/2 : ℝ) * x ^ 2)) := by
      funext x; congr 1; ring
    have hval : (∫ x : ℝ, Real.exp (-x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
      rw [hrw]
      have h := integral_gaussian (1/2 : ℝ)
      rw [h]
      congr 1
      ring
    rw [hval]
    rw [div_self (by positivity : Real.sqrt (2 * Real.pi) ≠ 0)]
  exact hfull

/-- Eigenfunctions are bounded by 1 (plain sines). -/
theorem abs_dirichletEigenfun_le_one (m : ℕ) (L x : ℝ) :
    |dirichletEigenfun m L x| ≤ 1 := by
  unfold dirichletEigenfun
  first
    | exact abs_sin_le_one _
    | exact Real.abs_sin_le_one _
    | (simp only []; exact abs_sin_le_one _)

/-- **Entry bound, decoded**: `|B^dec_{mn}(q)| ≤ decodedBumpMass(q) ≤ 1`. -/
theorem abs_decodedBumpMatrixElement_le_one
    (q : ℕ) (L : ℝ) (hL : 0 ≤ L) (m n : ℕ) :
    |decodedBumpMatrixElement 1 q L m n| ≤ 1 := by
  unfold decodedBumpMatrixElement
  have hb := decodedBumpMass_le_one q L hL
  have hcont : Continuous (fun x : ℝ =>
      dirichletEigenfun m L x * gaussBump 1 (x - (ppDecode q).center)
        * dirichletEigenfun n L x) := by
    first
      | fun_prop
      | (unfold dirichletEigenfun gaussBump; fun_prop)
      | (unfold dirichletEigenfun gaussBump; continuity)
  have hintg : IntervalIntegrable (fun x : ℝ =>
      dirichletEigenfun m L x * gaussBump 1 (x - (ppDecode q).center)
        * dirichletEigenfun n L x) MeasureTheory.volume 0 L :=
    hcont.intervalIntegrable 0 L
  calc |∫ x in (0:ℝ)..L,
        dirichletEigenfun m L x * gaussBump 1 (x - (ppDecode q).center)
          * dirichletEigenfun n L x|
      ≤ ∫ x in (0:ℝ)..L,
          |dirichletEigenfun m L x * gaussBump 1 (x - (ppDecode q).center)
            * dirichletEigenfun n L x| := by
        first
          | exact intervalIntegral.abs_integral_le_integral_abs hL
          | exact intervalIntegral.norm_integral_le_integral_norm hL
    _ ≤ ∫ x in (0:ℝ)..L, gaussBump 1 (x - (ppDecode q).center) := by
        apply intervalIntegral.integral_mono_on hL hintg.abs
          (intervalIntegrable_gaussBump_decoded 1 q L)
        intro x _
        have h1 := abs_dirichletEigenfun_le_one m L x
        have h2 := abs_dirichletEigenfun_le_one n L x
        have hg : 0 ≤ gaussBump 1 (x - (ppDecode q).center) := by
          unfold gaussBump; positivity
        calc |dirichletEigenfun m L x * gaussBump 1 (x - (ppDecode q).center)
              * dirichletEigenfun n L x|
            = |dirichletEigenfun m L x| * gaussBump 1 (x - (ppDecode q).center)
              * |dirichletEigenfun n L x| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hg]
          _ ≤ 1 * gaussBump 1 (x - (ppDecode q).center) * 1 := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_right h1 hg
              · exact h2
              · exact abs_nonneg _
              · positivity
          _ = gaussBump 1 (x - (ppDecode q).center) := by ring
    _ ≤ 1 := hb

/-- **Stone 5.5, decoded**: `|V^dec_{mn}| ≤ S1mass`-shaped sum. -/
theorem abs_decodedVmatrixElement_le
    (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (m n : ℕ) :
    |decodedVmatrixElement 1 qs w L m n| ≤ ∑ q ∈ qs, |w q| := by
  rw [decodedVmatrixElement_eq_sum_bumps]
  calc |∑ q ∈ qs, w q * decodedBumpMatrixElement 1 q L m n|
      ≤ ∑ q ∈ qs, |w q * decodedBumpMatrixElement 1 q L m n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ qs, |w q| := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul]
        calc |w q| * |decodedBumpMatrixElement 1 q L m n|
            ≤ |w q| * 1 :=
              mul_le_mul_of_nonneg_left
                (abs_decodedBumpMatrixElement_le_one q L hL m n) (abs_nonneg _)
          _ = |w q| := mul_one _

#print axioms decodedBumpMass_le_one
#print axioms abs_dirichletEigenfun_le_one
#print axioms abs_decodedBumpMatrixElement_le_one
#print axioms abs_decodedVmatrixElement_le

end

end RHFormalization
