/-
KboundUniform.lean

The SECOND anchor constant. KfunQ q := the frequency-decay prefactor from
Stone 3b at (delta, L) = (1, 1). Uniformly over all finite code sets:
  sum_{q in qs} |w q| * KfunQ q <= KboundConst.
Route: boundary bumps <= edge tail; derivMass <= (log q) * edge tail;
edge tail <= e^8 / q^3 (cubed: absorbs the log factor); |w| <= 2.
With Sbound this gives min(S, K/j) entry decay -> uniform Frobenius on V.
-/
import RHFormalization.SboundUniform
import RHFormalization.CosBumpFreqDecay

namespace RHFormalization
noncomputable section
open Real

/-- The Stone-3b prefactor at (delta, L) = (1, 1). -/
def KfunQ (q : ℕ) : ℝ :=
  gaussBump 1 (0 - Real.log q) + gaussBump 1 (1 - Real.log q)
    + bumpDerivMass 1 q 1

theorem KfunQ_nonneg (k : ℕ) : 0 ≤ KfunQ k := by
  unfold KfunQ
  have h1 := gaussBump_pos 1 one_pos (0 - Real.log k)
  have h2 := gaussBump_pos 1 one_pos (1 - Real.log k)
  have h3 := bumpDerivMass_nonneg 1 one_pos k 1 (by norm_num)
  linarith

/-- Stone 3b restated through the prefactor. -/
theorem abs_cosBumpIntegral_le_Kfun (q : ℕ) (j : ℝ) (hj : 0 < j) :
    |cosBumpIntegral 1 q 1 j| ≤ KfunQ q * 1 / (j * Real.pi) := by
  have h := abs_cosBumpIntegral_le_inv_freq 1 one_pos q 1 one_pos j hj
  unfold KfunQ
  exact h

/-- Cubed tail: the edge bump decays faster than q^{-3}. -/
theorem gaussTail_cube_le {k : ℕ} (hk : 1 ≤ k) :
    gaussBump 1 (Real.log (k : ℝ) - 1) ≤ Real.exp 8 * (((k : ℝ)) ^ 3)⁻¹ := by
  have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  set t := Real.log (k : ℝ) with ht
  have h1 : gaussBump 1 (t - 1) ≤ Real.exp (-(t - 1) ^ 2 / 2) := by
    unfold gaussBump
    simp only [one_pow, mul_one]
    apply div_le_self (le_of_lt (Real.exp_pos _))
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have h2 : Real.exp (-(t - 1) ^ 2 / 2) ≤ Real.exp (8 - 3 * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (t - 4)]
  have h3 : Real.exp (8 - 3 * t) = Real.exp 8 * (((k : ℝ)) ^ 3)⁻¹ := by
    rw [sub_eq_add_neg, Real.exp_add]
    congr 1
    rw [Real.exp_neg]
    congr 1
    rw [show 3 * t = t + t + t by ring, Real.exp_add, Real.exp_add,
      ht, Real.exp_log hkpos]
    ring
  calc gaussBump 1 (t - 1) ≤ Real.exp (-(t - 1) ^ 2 / 2) := h1
    _ ≤ Real.exp (8 - 3 * t) := h2
    _ = Real.exp 8 * (((k : ℝ)) ^ 3)⁻¹ := h3

/-- Derivative mass over the box is at most (log k) times the edge tail. -/
theorem bumpDerivMass_le_mul_tail {k : ℕ} (hk : 3 ≤ k) :
    bumpDerivMass 1 k 1
      ≤ Real.log (k : ℝ) * gaussBump 1 (Real.log (k : ℝ) - 1) := by
  have ht1 : 1 ≤ Real.log (k : ℝ) := one_le_log_of_three_le hk
  set t := Real.log (k : ℝ) with ht
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1,
      |(x - t) / (1:ℝ) ^ 2| * gaussBump 1 (x - t)
        ≤ t * gaussBump 1 (t - 1) := by
    intro x hx
    have hxt : |(x - t) / (1:ℝ) ^ 2| = |x - t| := by norm_num
    rw [hxt]
    have h1 : |x - t| ≤ t :=
      abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 : gaussBump 1 (x - t) ≤ gaussBump 1 (t - 1) := by
      apply gaussBump_one_le
      nlinarith [mul_nonneg
        (by linarith [hx.2] : (0:ℝ) ≤ 1 - x)
        (by linarith [hx.2, ht1] : (0:ℝ) ≤ 2 * t - x - 1)]
    exact mul_le_mul h1 h2
      (le_of_lt (gaussBump_pos 1 one_pos _)) (by linarith)
  unfold bumpDerivMass
  calc (∫ x in (0:ℝ)..1, |(x - Real.log (k:ℕ)) / (1:ℝ) ^ 2|
          * gaussBump 1 (x - Real.log (k:ℕ)))
      ≤ ∫ _x in (0:ℝ)..1, t * gaussBump 1 (t - 1) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (intervalIntegrable_derivMass 1 k 1) intervalIntegrable_const
        intro x hx
        exact hpt x hx
    _ = t * gaussBump 1 (t - 1) := by
        rw [intervalIntegral.integral_const]
        simp

/-- The prefactor decays like q^{-2}, with an absolute constant. -/
theorem Kfun_le {k : ℕ} (hk : 3 ≤ k) :
    KfunQ k ≤ 2 * Real.exp 8 * (((k : ℝ)) ^ 2)⁻¹ := by
  have ht1 : 1 ≤ Real.log (k : ℝ) := one_le_log_of_three_le hk
  have hk3R : (3:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k : ℝ) := by linarith
  set t := Real.log (k : ℝ) with ht
  set g := gaussBump 1 (t - 1) with hg
  have hgnn : 0 ≤ g := le_of_lt (gaussBump_pos 1 one_pos _)
  have b1 : gaussBump 1 (0 - t) ≤ g := by
    apply gaussBump_one_le
    nlinarith
  have b2 : gaussBump 1 (1 - t) ≤ g := by
    apply gaussBump_one_le
    nlinarith
  have b3 : bumpDerivMass 1 k 1 ≤ t * g := bumpDerivMass_le_mul_tail hk
  have tlek : t ≤ (k : ℝ) := by
    rw [ht]
    exact Real.log_le_self (le_of_lt hkpos)
  have gcube : g ≤ Real.exp 8 * (((k : ℝ)) ^ 3)⁻¹ :=
    gaussTail_cube_le (by omega)
  calc KfunQ k ≤ 2 * g + t * g := by
        unfold KfunQ
        linarith [b1, b2, b3]
    _ = (2 + t) * g := by ring
    _ ≤ (2 * (k : ℝ)) * g := by
        apply mul_le_mul_of_nonneg_right _ hgnn
        linarith
    _ ≤ (2 * (k : ℝ)) * (Real.exp 8 * (((k : ℝ)) ^ 3)⁻¹) := by
        apply mul_le_mul_of_nonneg_left gcube (by positivity)
    _ = 2 * Real.exp 8 * (((k : ℝ)) ^ 2)⁻¹ := by
        first
          | (field_simp; ring)
          | field_simp
          | ring

/-- The full weighted-prefactor series is summable. -/
theorem summable_weight_Kfun :
    Summable (fun k : ℕ => |ppWeightReal k| * KfunQ k) := by
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
    (fun n => mul_nonneg (abs_nonneg _) (KfunQ_nonneg _))
    (fun n => ?_)
    (((summable_nat_add_iff 3).mpr base).mul_left (2 * (2 * Real.exp 8)))
  calc |ppWeightReal (n + 3)| * KfunQ (n + 3)
      ≤ 2 * KfunQ (n + 3) :=
        mul_le_mul_of_nonneg_right (abs_ppWeightReal_le_two _) (KfunQ_nonneg _)
    _ ≤ 2 * (2 * Real.exp 8 * ((((n + 3 : ℕ)) : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (Kfun_le (by omega)) (by norm_num)
    _ = (2 * (2 * Real.exp 8)) * ((((n + 3 : ℕ)) : ℝ) ^ 2)⁻¹ := by ring

/-- **The second anchor constant.** -/
def KboundConst : ℝ := ∑' k : ℕ, |ppWeightReal k| * KfunQ k

/-- **Uniform K-bound**: one constant dominates the weighted Stone-3b
prefactor over EVERY finite code set. -/
theorem Kbound_uniform (qs : Finset ℕ) :
    ∑ q ∈ qs, |ppWeightReal q| * KfunQ q ≤ KboundConst := by
  first
    | exact sum_le_tsum qs
        (fun i _ => mul_nonneg (abs_nonneg _) (KfunQ_nonneg _))
        summable_weight_Kfun
    | exact Finset.sum_le_tsum qs
        (fun i _ => mul_nonneg (abs_nonneg _) (KfunQ_nonneg _))
        summable_weight_Kfun
    | exact summable_weight_Kfun.sum_le_tsum qs
        (fun i _ => mul_nonneg (abs_nonneg _) (KfunQ_nonneg _))

#print axioms KfunQ_nonneg
#print axioms abs_cosBumpIntegral_le_Kfun
#print axioms gaussTail_cube_le
#print axioms bumpDerivMass_le_mul_tail
#print axioms Kfun_le
#print axioms summable_weight_Kfun
#print axioms Kbound_uniform

end
end RHFormalization
