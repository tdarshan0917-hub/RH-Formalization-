/-
SupVBound.lean

THE SUP-ANCHOR (Proposition A/B.UNIFORM-LOWER-BOUND's estimate). The
position-space prime potential is uniformly bounded on the box [0,1] by one
absolute constant, over EVERY finite code set:
  sup_{x in [0,1]} |primePotentialFn 1 qs ppWeightReal x| <= SupVConst.
Per-bump: flat 1/sqrt(2*pi) for k < 3, edge Gaussian tail for k >= 3 (the
banked (1-x)(2t-x-1) edge comparison). Powers the manuscript's uniform shift
M, Lemma D.R->infty tail convergence, and D.TAIL-DENSITY.
-/
import RHFormalization.KboundUniform

namespace RHFormalization
noncomputable section
open Real

/-- The bump never exceeds its peak 1/sqrt(2*pi) (at delta = 1). -/
theorem gaussBump_le_peak (y : ℝ) : gaussBump 1 y ≤ 1 / Real.sqrt (2 * Real.pi) := by
  unfold gaussBump
  simp only [one_pow, mul_one]
  have hexp : Real.exp (-y ^ 2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])
  gcongr

/-- Pointwise envelope for a single bump on the box: flat for small k,
edge tail for k >= 3. -/
def bumpEnvelope (k : ℕ) : ℝ :=
  if 3 ≤ k then gaussBump 1 (Real.log (k : ℝ) - 1)
  else 1 / Real.sqrt (2 * Real.pi)

theorem bumpEnvelope_nonneg (k : ℕ) : 0 ≤ bumpEnvelope k := by
  unfold bumpEnvelope
  split_ifs
  · exact le_of_lt (gaussBump_pos 1 one_pos _)
  · positivity

/-- On the box, each bump is dominated by its envelope. -/
theorem gaussBump_le_envelope {k : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    gaussBump 1 (x - Real.log (k : ℝ)) ≤ bumpEnvelope k := by
  unfold bumpEnvelope
  split_ifs with hk
  · have ht1 : 1 ≤ Real.log (k : ℝ) := one_le_log_of_three_le hk
    apply gaussBump_one_le
    set t := Real.log (k : ℝ)
    nlinarith [mul_nonneg
      (by linarith [hx.2] : (0:ℝ) ≤ 1 - x)
      (by linarith [hx.2, ht1] : (0:ℝ) ≤ 2 * t - x - 1)]
  · exact gaussBump_le_peak _

/-- The weighted envelope series is summable. -/
theorem summable_weight_envelope :
    Summable (fun k : ℕ => |ppWeightReal k| * bumpEnvelope k) := by
  have base : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
    first
      | exact Real.summable_nat_pow_inv.mpr one_lt_two
      | exact Real.summable_nat_pow_inv.2 (by norm_num)
      | { have h := Real.summable_one_div_nat_rpow.mpr
            (by norm_num : (1:ℝ) < 2)
          simpa [Real.rpow_natCast, one_div] using h }
  rw [← summable_nat_add_iff 3]
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (bumpEnvelope_nonneg _))
    (fun n => ?_)
    (((summable_nat_add_iff 3).mpr base).mul_left (2 * Real.exp 8))
  have henv : bumpEnvelope (n + 3) = gaussBump 1 (Real.log ((n + 3 : ℕ) : ℝ) - 1) := by
    unfold bumpEnvelope
    rw [if_pos (by omega)]
  calc |ppWeightReal (n + 3)| * bumpEnvelope (n + 3)
      ≤ 2 * bumpEnvelope (n + 3) :=
        mul_le_mul_of_nonneg_right (abs_ppWeightReal_le_two _) (bumpEnvelope_nonneg _)
    _ = 2 * gaussBump 1 (Real.log ((n + 3 : ℕ) : ℝ) - 1) := by rw [henv]
    _ ≤ 2 * (Real.exp 8 * ((((n + 3 : ℕ)) : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (gaussTail_le (by omega)) (by norm_num)
    _ = (2 * Real.exp 8) * ((((n + 3 : ℕ)) : ℝ) ^ 2)⁻¹ := by ring

/-- **The sup-anchor constant.** -/
def SupVConst : ℝ := ∑' k : ℕ, |ppWeightReal k| * bumpEnvelope k

/-- **THE SUP-ANCHOR (A/B.UNIFORM-LOWER-BOUND estimate).** The position-space
prime potential is uniformly bounded on the box, over every finite code set. -/
theorem supV_uniform (qs : Finset ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |primePotentialFn 1 qs ppWeightReal x| ≤ SupVConst := by
  unfold primePotentialFn
  calc |∑ q ∈ qs, ppWeightReal q * gaussBump 1 (x - Real.log q)|
      ≤ ∑ q ∈ qs, |ppWeightReal q * gaussBump 1 (x - Real.log q)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ qs, |ppWeightReal q| * bumpEnvelope q := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul, abs_of_pos (gaussBump_pos 1 one_pos _)]
        exact mul_le_mul_of_nonneg_left
          (gaussBump_le_envelope hx) (abs_nonneg _)
    _ ≤ SupVConst := by
        first
          | exact sum_le_tsum qs
              (fun i _ => mul_nonneg (abs_nonneg _) (bumpEnvelope_nonneg _))
              summable_weight_envelope
          | exact summable_weight_envelope.sum_le_tsum qs
              (fun i _ => mul_nonneg (abs_nonneg _) (bumpEnvelope_nonneg _))

/-- Tail form (Lemma D.R->infty engine): the potential over any code set
DISJOINT from the small codes is bounded by the corresponding tail sum. -/
theorem supV_tail_le (qs : Finset ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |primePotentialFn 1 qs ppWeightReal x|
      ≤ ∑ q ∈ qs, |ppWeightReal q| * bumpEnvelope q := by
  unfold primePotentialFn
  calc |∑ q ∈ qs, ppWeightReal q * gaussBump 1 (x - Real.log q)|
      ≤ ∑ q ∈ qs, |ppWeightReal q * gaussBump 1 (x - Real.log q)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ qs, |ppWeightReal q| * bumpEnvelope q := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul, abs_of_pos (gaussBump_pos 1 one_pos _)]
        exact mul_le_mul_of_nonneg_left
          (gaussBump_le_envelope hx) (abs_nonneg _)

#print axioms gaussBump_le_peak
#print axioms gaussBump_le_envelope
#print axioms summable_weight_envelope
#print axioms supV_uniform
#print axioms supV_tail_le

end
end RHFormalization
