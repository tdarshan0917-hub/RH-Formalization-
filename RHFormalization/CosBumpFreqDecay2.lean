/-
CosBumpFreqDecay2.lean

Stone 3c: SECOND integration by parts. |C_j(q)| <= K2(q) * (L/(j*pi))^2 + 
boundary/omega terms — packaged as the clean 1/j^2 decay needed for
absolutely summable row sums (Schur form bound). W'' is the same Gaussian
family; all masses get the anchor treatment downstream.
-/
import RHFormalization.CosBumpFreqDecay
import Mathlib

namespace RHFormalization
noncomputable section
open Real intervalIntegral

/-- Second derivative of the bump: W''(x) = ((x^2 - δ^2)/δ^4)·W(x). -/
theorem hasDerivAt_gaussBump_deriv (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (fun y => -(y / δ ^ 2) * gaussBump δ y)
      (((x ^ 2 - δ ^ 2) / δ ^ 4) * gaussBump δ x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y / δ ^ 2)) (-(1 / δ ^ 2)) x := by
    simpa using ((hasDerivAt_id x).div_const (δ ^ 2)).neg
  have h2 := hasDerivAt_gaussBump δ hδ x
  have h3 := h1.mul h2
  convert h3 using 1
  have hδ4 : δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
  field_simp
  ring

/-- The sine-weighted derivative integral. -/
def sinBumpDerivIntegral (δ : ℝ) (q : ℕ) (L : ℝ) (ω : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..L, Real.sin (ω * x) * (-((x - Real.log q) / δ ^ 2)
    * gaussBump δ (x - Real.log q))

/-- Second-derivative mass over the box. -/
def bumpDeriv2Mass (δ : ℝ) (q : ℕ) (L : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..L,
    |((x - Real.log q) ^ 2 - δ ^ 2) / δ ^ 4| * gaussBump δ (x - Real.log q)

theorem bumpDeriv2Mass_nonneg (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    0 ≤ bumpDeriv2Mass δ q L := by
  unfold bumpDeriv2Mass
  apply intervalIntegral.integral_nonneg hL
  intro x _
  exact mul_nonneg (abs_nonneg _) (le_of_lt (gaussBump_pos δ hδ _))

/-- IBP on the sine integral: bounds it by (boundary W' + ∫|W''|)/ω. -/
theorem abs_sinBumpDerivIntegral_le
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (hL : 0 < L) (ω : ℝ) (hω : 0 < ω) :
    |sinBumpDerivIntegral δ q L ω|
      ≤ (|Real.log q / δ ^ 2| * gaussBump δ (0 - Real.log q)
          + |(L - Real.log q) / δ ^ 2| * gaussBump δ (L - Real.log q)
          + bumpDeriv2Mass δ q L) / ω := by
  set c : ℝ := Real.log q with hc
  set U : ℝ → ℝ := fun x => -((x - c) / δ ^ 2) * gaussBump δ (x - c) with hU
  set U' : ℝ → ℝ := fun x => ((x - c) ^ 2 - δ ^ 2) / δ ^ 4 * gaussBump δ (x - c)
    with hU'
  have hUd : ∀ x ∈ Set.Ioo (min (0:ℝ) L) (max 0 L), HasDerivAt U (U' x) x := by
    intro x _
    have := (hasDerivAt_gaussBump_deriv δ hδ (x - c)).comp x
      ((hasDerivAt_id x).sub_const c)
    simpa [hU, hU'] using this
  set G : ℝ → ℝ := fun x => -(Real.cos (ω * x)) / ω with hG
  have hGd : ∀ x ∈ Set.Ioo (min (0:ℝ) L) (max 0 L),
      HasDerivAt G (Real.sin (ω * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => ω * y) ω x := by
      simpa using (hasDerivAt_id x).const_mul ω
    have h2 : HasDerivAt (fun y : ℝ => Real.cos (ω * y))
        (-Real.sin (ω * x) * ω) x := (Real.hasDerivAt_cos _).comp x h1
    have h3 := (h2.neg).div_const ω
    convert h3 using 1
    field_simp
  have hUcont : Continuous U := by
    simp only [hU]; unfold gaussBump; fun_prop
  have hGcont : Continuous G := by
    simp only [hG]; fun_prop
  have hU'int : IntervalIntegrable U' MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    simp only [hU']; unfold gaussBump; fun_prop
  have hsinint : IntervalIntegrable (fun x => Real.sin (ω * x))
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable; fun_prop
  have hIBP : (∫ x in (0:ℝ)..L, U x * Real.sin (ω * x))
      = U L * G L - U 0 * G 0 - ∫ x in (0:ℝ)..L, U' x * G x := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hUcont.continuousOn hGcont.continuousOn hUd hGd hU'int hsinint
  have hEq : sinBumpDerivIntegral δ q L ω
      = ∫ x in (0:ℝ)..L, U x * Real.sin (ω * x) := by
    unfold sinBumpDerivIntegral
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hU, hc]
    ring
  rw [hEq, hIBP]
  have hGb : ∀ x : ℝ, |G x| ≤ 1 / ω := by
    intro x
    simp only [hG, abs_div, abs_neg, abs_of_pos hω]
    gcongr
    exact abs_cos_le_one _
  have hUabs : ∀ x : ℝ, |U x| = |(x - c) / δ ^ 2| * gaussBump δ (x - c) := by
    intro x
    simp only [hU]
    rw [abs_mul, abs_neg, abs_of_pos (gaussBump_pos δ hδ _)]
  have hb1 : |U L * G L|
      ≤ |(L - c) / δ ^ 2| * gaussBump δ (L - c) / ω := by
    rw [abs_mul, hUabs]
    have := hGb L
    calc |(L - c) / δ ^ 2| * gaussBump δ (L - c) * |G L|
        ≤ |(L - c) / δ ^ 2| * gaussBump δ (L - c) * (1 / ω) := by
          apply mul_le_mul_of_nonneg_left this
          exact mul_nonneg (abs_nonneg _) (le_of_lt (gaussBump_pos δ hδ _))
      _ = |(L - c) / δ ^ 2| * gaussBump δ (L - c) / ω := by ring
  have hb0 : |U 0 * G 0|
      ≤ |(0 - c) / δ ^ 2| * gaussBump δ (0 - c) / ω := by
    rw [abs_mul, hUabs]
    have := hGb 0
    calc |(0 - c) / δ ^ 2| * gaussBump δ (0 - c) * |G 0|
        ≤ |(0 - c) / δ ^ 2| * gaussBump δ (0 - c) * (1 / ω) := by
          apply mul_le_mul_of_nonneg_left this
          exact mul_nonneg (abs_nonneg _) (le_of_lt (gaussBump_pos δ hδ _))
      _ = |(0 - c) / δ ^ 2| * gaussBump δ (0 - c) / ω := by ring
  have hUVint : IntervalIntegrable (fun x => U' x * G x)
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    simp only [hU', hG]; unfold gaussBump; fun_prop
  have hbI : |∫ x in (0:ℝ)..L, U' x * G x| ≤ bumpDeriv2Mass δ q L / ω := by
    have hptw : ∀ x ∈ Set.Icc (0:ℝ) 1 ∪ Set.Icc 0 L, True := fun _ _ => trivial
    calc |∫ x in (0:ℝ)..L, U' x * G x|
        ≤ ∫ x in (0:ℝ)..L, |U' x * G x| := by
          have := intervalIntegral.norm_integral_le_integral_norm
            (f := fun x => U' x * G x) (μ := MeasureTheory.volume) (le_of_lt hL)
          simpa using this
      _ ≤ ∫ x in (0:ℝ)..L,
            |((x - c) ^ 2 - δ ^ 2) / δ ^ 4| * gaussBump δ (x - c) * (1/ω) := by
          apply intervalIntegral.integral_mono_on (le_of_lt hL)
          · exact hUVint.abs
          · apply Continuous.intervalIntegrable
            unfold gaussBump; fun_prop
          · intro x _
            rw [abs_mul]
            have h1 : |U' x| = |((x - c) ^ 2 - δ ^ 2) / δ ^ 4|
                * gaussBump δ (x - c) := by
              simp only [hU']
              rw [abs_mul, abs_of_pos (gaussBump_pos δ hδ _)]
            rw [h1]
            exact mul_le_mul_of_nonneg_left (hGb x)
              (mul_nonneg (abs_nonneg _) (le_of_lt (gaussBump_pos δ hδ _)))
      _ = (∫ x in (0:ℝ)..L,
            |((x - c) ^ 2 - δ ^ 2) / δ ^ 4| * gaussBump δ (x - c)) * (1/ω) := by
          rw [intervalIntegral.integral_mul_const]
      _ = bumpDeriv2Mass δ q L * (1/ω) := by rfl
      _ = bumpDeriv2Mass δ q L / ω := by ring
  calc |U L * G L - U 0 * G 0 - ∫ x in (0:ℝ)..L, U' x * G x|
      ≤ |U L * G L - U 0 * G 0| + |∫ x in (0:ℝ)..L, U' x * G x| := abs_sub _ _
    _ ≤ (|U L * G L| + |U 0 * G 0|) + |∫ x in (0:ℝ)..L, U' x * G x| := by
        have habs : |U L * G L - U 0 * G 0| ≤ |U L * G L| + |U 0 * G 0| := by
          first
            | exact abs_sub_le_add_abs _ _
            | exact abs_sub _ _
            | { have h := abs_add (U L * G L) (-(U 0 * G 0))
                simpa [abs_neg, sub_eq_add_neg] using h }
            | { have h := norm_sub_le (U L * G L) (U 0 * G 0)
                simpa using h }
        linarith
    _ ≤ (|Real.log q / δ ^ 2| * gaussBump δ (0 - Real.log q)
          + |(L - Real.log q) / δ ^ 2| * gaussBump δ (L - Real.log q)
          + bumpDeriv2Mass δ q L) / ω := by
        have hz : |(0 - c) / δ ^ 2| = |Real.log q / δ ^ 2| := by
          rw [hc]; rw [zero_sub, neg_div, abs_neg]
        rw [add_div, add_div]
        have hb0' := hb0
        rw [hz] at hb0'
        have hc0 : (0:ℝ) - c = 0 - Real.log q := by rw [hc]
        have hcL : L - c = L - Real.log q := by rw [hc]
        rw [hc0] at hb0'
        rw [hcL] at hb1
        linarith [hb1, hb0', hbI]

#print axioms hasDerivAt_gaussBump_deriv
#print axioms abs_sinBumpDerivIntegral_le

end
end RHFormalization
