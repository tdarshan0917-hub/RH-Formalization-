/-
SboundUniform.lean

THE ANCHOR ESTIMATE. S(qs) := sum_{q in qs} |w(q)| * bumpMass(q) is bounded
by one absolute constant, uniformly over ALL finite code sets — in particular
along the entire galerkin stage exhaustion. Ingredients:
  (1) |ppWeightReal| <= 2                       (log y <= y-1)
  (2) bumpMass 1 k 1 <= gaussTail for k >= 3    (box [0,1] vs center log k >= 1)
  (3) gaussTail <= e^8 / k^2 for ALL k >= 1     ((t-1)^2/2 >= 2t-8, disc < 0)
This is the density-normalized S(t,R) bound: the load-bearing constant for the
uniform shift, uniform Weyl control, and both F/R convergence fronts.
-/
import RHFormalization.GalerkinStageSequence
import Mathlib

namespace RHFormalization
noncomputable section
open Real

/-- Gaussian bump comparison: larger squared argument, smaller bump. -/
theorem gaussBump_one_le {a b : ℝ} (h : b ^ 2 ≤ a ^ 2) :
    gaussBump 1 a ≤ gaussBump 1 b := by
  unfold gaussBump
  simp only [one_pow, mul_one]
  have hD : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  have hexp : Real.exp (-a ^ 2 / 2) ≤ Real.exp (-b ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  gcongr

/-- (1) The arithmetic prime weight is uniformly at most 2. -/
theorem abs_ppWeightReal_le_two (k : ℕ) : |ppWeightReal k| ≤ 2 := by
  have heq : ppWeightReal k = (ppDecode k).weightReal := by
    unfold ppWeightReal
    rw [PrimePowerPair.weightC]
    exact Complex.ofReal_re _
  rw [heq]
  set q := ppDecode k with hq
  simp only [PrimePowerPair.weightReal]
  split_ifs with hval
  · have hp2 : 2 ≤ q.p := hval.1.two_le
    have hp2R : (2:ℝ) ≤ (q.p : ℝ) := by exact_mod_cast hp2
    have hppos : (0:ℝ) < (q.p : ℝ) := by linarith
    have hsqp_pos : 0 < Real.sqrt (q.p : ℝ) := Real.sqrt_pos.mpr hppos
    have hple : q.p ≤ q.natValue := by
      unfold PrimePowerPair.natValue
      exact Nat.le_self_pow hval.2.ne' q.p
    have hpleR : (q.p : ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast hple
    have hnat_pos : (0:ℝ) < ((q.natValue : ℕ) : ℝ) := lt_of_lt_of_le hppos hpleR
    have hsqn_pos : 0 < Real.sqrt ((q.natValue : ℕ) : ℝ) := Real.sqrt_pos.mpr hnat_pos
    have hsqrt_le : Real.sqrt (q.p : ℝ) ≤ Real.sqrt ((q.natValue : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hpleR
    have hlog_nn : 0 ≤ Real.log (q.p : ℝ) := Real.log_nonneg (by linarith)
    have h1 : Real.log (q.p : ℝ) / Real.sqrt ((q.natValue : ℕ) : ℝ)
        ≤ Real.log (q.p : ℝ) / Real.sqrt (q.p : ℝ) := by
      apply div_le_div_of_nonneg_left hlog_nn hsqp_pos hsqrt_le
    have h2 : Real.log (q.p : ℝ) ≤ 2 * Real.sqrt (q.p : ℝ) := by
      have hls : Real.log (Real.sqrt (q.p : ℝ)) ≤ Real.sqrt (q.p : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hsqp_pos
      have hhalf : Real.log (Real.sqrt (q.p : ℝ)) = Real.log (q.p : ℝ) / 2 :=
        Real.log_sqrt (le_of_lt hppos)
      nlinarith
    have h3 : Real.log (q.p : ℝ) / Real.sqrt (q.p : ℝ) ≤ 2 := by
      have hstep : Real.log (q.p : ℝ) / Real.sqrt (q.p : ℝ)
          ≤ 2 * Real.sqrt (q.p : ℝ) / Real.sqrt (q.p : ℝ) := by
        gcongr
      calc Real.log (q.p : ℝ) / Real.sqrt (q.p : ℝ)
          ≤ 2 * Real.sqrt (q.p : ℝ) / Real.sqrt (q.p : ℝ) := hstep
        _ = 2 := by field_simp
    rw [abs_of_nonneg (div_nonneg hlog_nn (Real.sqrt_nonneg _))]
    linarith
  · simp

/-- bumpMass is nonnegative. -/
theorem bumpMass_nonneg' (q : ℕ) : 0 ≤ bumpMass 1 q 1 := by
  unfold bumpMass
  exact intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ => le_of_lt (gaussBump_pos 1 one_pos _))

/-- log k >= 1 once k >= 3 (since e < 3). -/
theorem one_le_log_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    1 ≤ Real.log (k : ℝ) := by
  have h3 : (3:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog3 : 1 < Real.log 3 := by
    have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    first
      | exact (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)).mpr hexp
      | exact Real.lt_log_iff_exp_lt.mpr hexp
  have hmono : Real.log 3 ≤ Real.log (k : ℝ) := by
    first
      | exact Real.log_le_log (by norm_num) h3
      | exact Real.log_le_log_of_le h3
      | exact (Real.log_le_log_iff (by norm_num) (by linarith)).mpr h3
      | gcongr
  linarith

/-- (2) Tail bound: for k >= 3, the box mass is at most the edge bump value. -/
theorem bumpMass_le_tail {k : ℕ} (hk : 3 ≤ k) :
    bumpMass 1 k 1 ≤ gaussBump 1 (Real.log (k : ℝ) - 1) := by
  have hlog := one_le_log_of_three_le hk
  set t := Real.log (k : ℝ) with ht
  unfold bumpMass
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1,
      gaussBump 1 (x - t) ≤ gaussBump 1 (t - 1) := by
    intro x hx
    apply gaussBump_one_le
    nlinarith [hx.1, hx.2]
  calc (∫ x in (0:ℝ)..1, gaussBump 1 (x - Real.log (k:ℕ)))
      ≤ ∫ _x in (0:ℝ)..1, gaussBump 1 (t - 1) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (intervalIntegrable_gaussBump 1 k 1)
          intervalIntegrable_const
        intro x hx
        exact hpt x hx
    _ = gaussBump 1 (t - 1) := by
        rw [intervalIntegral.integral_const]
        simp

/-- (3) Global tail estimate: gaussTail(k) <= e^8 / k^2 for every k >= 1. -/
theorem gaussTail_le {k : ℕ} (hk : 1 ≤ k) :
    gaussBump 1 (Real.log (k : ℝ) - 1) ≤ Real.exp 8 * (((k : ℝ)) ^ 2)⁻¹ := by
  have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  set t := Real.log (k : ℝ) with ht
  have h1 : gaussBump 1 (t - 1) ≤ Real.exp (-(t - 1) ^ 2 / 2) := by
    unfold gaussBump
    simp only [one_pow, mul_one]
    apply div_le_self (le_of_lt (Real.exp_pos _))
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have h2 : Real.exp (-(t - 1) ^ 2 / 2) ≤ Real.exp (8 - 2 * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (t - 3)]
  have h3 : Real.exp (8 - 2 * t) = Real.exp 8 * (((k : ℝ)) ^ 2)⁻¹ := by
    rw [sub_eq_add_neg, Real.exp_add]
    congr 1
    rw [Real.exp_neg]
    congr 1
    rw [show 2 * t = t + t by ring, Real.exp_add, ht, Real.exp_log hkpos]
    ring
  calc gaussBump 1 (t - 1) ≤ Real.exp (-(t - 1) ^ 2 / 2) := h1
    _ ≤ Real.exp (8 - 2 * t) := h2
    _ = Real.exp 8 * (((k : ℝ)) ^ 2)⁻¹ := h3

/-- The full weighted-mass series over all codes is summable. -/
theorem summable_weight_bumpMass :
    Summable (fun k : ℕ => |ppWeightReal k| * bumpMass 1 k 1) := by
  have base : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
    first
      | exact Real.summable_nat_pow_inv.mpr one_lt_two
      | exact Real.summable_nat_pow_inv.2 (by norm_num)
      | simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 2 ≤ 2)
      | { have h := Real.summable_one_div_nat_rpow.mpr
            (by norm_num : (1:ℝ) < 2)
          simpa [Real.rpow_natCast, one_div] using h }
  rw [← summable_nat_add_iff 3]
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (bumpMass_nonneg' _))
    (fun n => ?_)
    (((summable_nat_add_iff 3).mpr base).mul_left (2 * Real.exp 8))
  calc |ppWeightReal (n + 3)| * bumpMass 1 (n + 3) 1
      ≤ 2 * bumpMass 1 (n + 3) 1 :=
        mul_le_mul_of_nonneg_right (abs_ppWeightReal_le_two _) (bumpMass_nonneg' _)
    _ ≤ 2 * gaussBump 1 (Real.log ((n + 3 : ℕ) : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left (bumpMass_le_tail (by omega)) (by norm_num)
    _ ≤ 2 * (Real.exp 8 * ((((n + 3 : ℕ) : ℝ)) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (gaussTail_le (by omega)) (by norm_num)
    _ = (2 * Real.exp 8) * ((((n + 3 : ℕ) : ℝ)) ^ 2)⁻¹ := by ring

/-- **The anchor constant.** -/
def SboundConst : ℝ := ∑' k : ℕ, |ppWeightReal k| * bumpMass 1 k 1

/-- **THE ANCHOR ESTIMATE (uniform S-bound).** One constant dominates the
weighted bump mass over EVERY finite code set — in particular every stage. -/
theorem Sbound_uniform (qs : Finset ℕ) :
    ∑ q ∈ qs, |ppWeightReal q| * bumpMass 1 q 1 ≤ SboundConst := by
  first
    | exact sum_le_tsum qs
        (fun i _ => mul_nonneg (abs_nonneg _) (bumpMass_nonneg' _))
        summable_weight_bumpMass
    | exact Finset.sum_le_tsum qs
        (fun i _ => mul_nonneg (abs_nonneg _) (bumpMass_nonneg' _))
        summable_weight_bumpMass
    | exact summable_weight_bumpMass.sum_le_tsum qs
        (fun i _ => mul_nonneg (abs_nonneg _) (bumpMass_nonneg' _))

/-- The anchor estimate along the galerkin stage exhaustion. -/
theorem Sbound_uniform_stage (n : ℕ) :
    ∑ q ∈ activePrimePowerCodesCenterBelow ((n : ℝ) + 1),
      |ppWeightReal q| * bumpMass 1 q 1 ≤ SboundConst :=
  Sbound_uniform _

#print axioms abs_ppWeightReal_le_two
#print axioms bumpMass_le_tail
#print axioms gaussTail_le
#print axioms summable_weight_bumpMass
#print axioms Sbound_uniform
#print axioms Sbound_uniform_stage

end
end RHFormalization
