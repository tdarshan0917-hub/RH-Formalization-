-- SENTINEL: S3-v3
import RHFormalization.AdaptiveSpikeDefectBound
import RHFormalization.AdaptiveStageMassBridge
import Mathlib

/-!
# The weighted stage defect sum (defect-gate Step 1(C))

Sums the banked per-spike bound (`abs_adaptiveSpikeDefectT_le`) over the
active spikes, weighted by ‖q.weightC‖, against the a-uniform stage rate:

  Σ_q ‖q.weightC‖·|adaptiveSpikeDefectT c n q.center t|
    ≤ adaptiveStageMass n · adaptiveStageDefectRate c n t

with `adaptiveStageDefectRate` obtained from the per-spike bound by
monotonizing over 0 ≤ a ≤ admR n ≤ L_n: (L−a)/(2L) ≤ 1/2 and |a| ≤ admR n.
Combined with `adaptiveStageMass_le_sqrt`, the G4 rate structure is
mass ~ √(n+2) against rate pieces O(1/L_n), O(1/(n+2)) (after t-integration
of the Gaussian factor with N_n/L_n ≥ n+2), and O(log N_n / L_n).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- The schedule cutoff sits inside the adaptive window. -/
theorem admR_le_adaptiveL (c : ℝ) (n : ℕ) : admR n ≤ adaptiveL c n := by
  have h1 : admR n ≤ admL n := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have hlog : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 2 - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    unfold admR admL
    nlinarith [hlog, hx, sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 1)]
  exact h1.trans (admL_le_adaptiveL c n)

/-- **The a-uniform per-stage defect rate** (t-domain): the per-spike bound
monotonized over the active window `0 ≤ a ≤ admR n`. -/
def adaptiveStageDefectRate (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (1 / 2) * ((1 / Real.pi) *
      ((Real.pi / adaptiveL c n)
          * (1 + admR n * Real.sqrt (Real.pi / t))
        + Real.exp (-(t * ((adaptiveN c n : ℝ)
                * (Real.pi / adaptiveL c n)) ^ 2) / 2)
            * Real.sqrt (2 * Real.pi / t)))
    + (1 / (2 * adaptiveL c n))
        * ((1 / Real.pi) * (1 + Real.log (adaptiveN c n)))

/-- The per-spike bound, monotonized: uniform over active centers. -/
theorem abs_adaptiveSpikeDefectT_le_rate (c : ℝ) (n : ℕ) (t : ℝ)
    (ht : 0 < t) (q : PrimePowerPair)
    (hq : q ∈ activePrimePowerPairsCenterBelow (admR n)) :
    |adaptiveSpikeDefectT c n q.center t|
      ≤ adaptiveStageDefectRate c n t := by
  obtain ⟨hval, hcR⟩ := (activePrimePowerPairsCenterBelow_mem (admR n) q).mp hq
  have ha0 : 0 ≤ q.center := primePowerPair_center_nonneg_of_valid q hval
  have hRL : admR n ≤ adaptiveL c n := admR_le_adaptiveL c n
  have haL : q.center ≤ adaptiveL c n := hcR.trans hRL
  have hL : (0:ℝ) < adaptiveL c n := adaptiveL_pos c n
  refine (abs_adaptiveSpikeDefectT_le c n q.center t ht ha0 haL).trans ?_
  unfold adaptiveStageDefectRate
  have hsqrtnn : (0:ℝ) ≤ Real.sqrt (Real.pi / t) := Real.sqrt_nonneg _
  -- inner factor monotone: 1 + |a|√ ≤ 1 + R√
  have hinner : 1 + |q.center| * Real.sqrt (Real.pi / t)
      ≤ 1 + admR n * Real.sqrt (Real.pi / t) := by
    have habs : |q.center| ≤ admR n := by
      rw [abs_of_nonneg ha0]; exact hcR
    nlinarith [hsqrtnn, habs]
  -- prefactor monotone: (L−a)/(2L) ≤ 1/2
  have hpre : (adaptiveL c n - q.center) / (2 * adaptiveL c n) ≤ 1 / 2 := by
    have hnum : adaptiveL c n - q.center ≤ adaptiveL c n := by linarith
    calc (adaptiveL c n - q.center) / (2 * adaptiveL c n)
        ≤ adaptiveL c n / (2 * adaptiveL c n) := by gcongr
      _ = 1 / 2 := by field_simp
  have hprenn : (0:ℝ) ≤ (adaptiveL c n - q.center) / (2 * adaptiveL c n) :=
    div_nonneg (sub_nonneg.mpr haL) (by positivity)
  -- the bracketed cosine-leg quantity, at a and at the sup
  have hbrknn : (0:ℝ) ≤ (1 / Real.pi) *
      ((Real.pi / adaptiveL c n)
          * (1 + |q.center| * Real.sqrt (Real.pi / t))
        + Real.exp (-(t * ((adaptiveN c n : ℝ)
                * (Real.pi / adaptiveL c n)) ^ 2) / 2)
            * Real.sqrt (2 * Real.pi / t)) := by positivity
  have hbrk : (1 / Real.pi) *
      ((Real.pi / adaptiveL c n)
          * (1 + |q.center| * Real.sqrt (Real.pi / t))
        + Real.exp (-(t * ((adaptiveN c n : ℝ)
                * (Real.pi / adaptiveL c n)) ^ 2) / 2)
            * Real.sqrt (2 * Real.pi / t))
      ≤ (1 / Real.pi) *
      ((Real.pi / adaptiveL c n)
          * (1 + admR n * Real.sqrt (Real.pi / t))
        + Real.exp (-(t * ((adaptiveN c n : ℝ)
                * (Real.pi / adaptiveL c n)) ^ 2) / 2)
            * Real.sqrt (2 * Real.pi / t)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine add_le_add ?_ le_rfl
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  refine add_le_add ?_ le_rfl
  calc (adaptiveL c n - q.center) / (2 * adaptiveL c n) * ((1 / Real.pi) *
        ((Real.pi / adaptiveL c n)
            * (1 + |q.center| * Real.sqrt (Real.pi / t))
          + Real.exp (-(t * ((adaptiveN c n : ℝ)
                  * (Real.pi / adaptiveL c n)) ^ 2) / 2)
              * Real.sqrt (2 * Real.pi / t)))
      ≤ (1 / 2) * ((1 / Real.pi) *
        ((Real.pi / adaptiveL c n)
            * (1 + admR n * Real.sqrt (Real.pi / t))
          + Real.exp (-(t * ((adaptiveN c n : ℝ)
                  * (Real.pi / adaptiveL c n)) ^ 2) / 2)
              * Real.sqrt (2 * Real.pi / t))) := by
        exact mul_le_mul hpre hbrk hbrknn (by norm_num)

/-- **The weighted stage defect sum bound (Step 1(C))**. -/
theorem weighted_adaptiveSpikeDefect_sum_le (c : ℝ) (n : ℕ) (t : ℝ)
    (ht : 0 < t) :
    ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        ‖q.weightC‖ * |adaptiveSpikeDefectT c n q.center t|
      ≤ adaptiveStageMass n * adaptiveStageDefectRate c n t := by
  have hstep : ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        ‖q.weightC‖ * |adaptiveSpikeDefectT c n q.center t|
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        ‖q.weightC‖ * adaptiveStageDefectRate c n t := by
    refine Finset.sum_le_sum fun q hq => ?_
    exact mul_le_mul_of_nonneg_left
      (abs_adaptiveSpikeDefectT_le_rate c n t ht q hq) (norm_nonneg _)
  refine hstep.trans ?_
  rw [← Finset.sum_mul]
  rfl

#print axioms admR_le_adaptiveL
#print axioms adaptiveStageDefectRate
#print axioms abs_adaptiveSpikeDefectT_le_rate
#print axioms weighted_adaptiveSpikeDefect_sum_le

end

end RHFormalization
