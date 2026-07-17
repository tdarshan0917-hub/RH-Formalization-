-- SENTINEL: E3b-v5
import RHFormalization.AdaptiveScheduleGrowthBounds
import RHFormalization.HsumUnconditional
import Mathlib

/-!
# The s-free overlap rate and its √(n+2) decay (defect-gate E3b)

  overlapRateBound c n := (1/(2L)) + πR/(2L) + 1/M + (1+log N)/(2πL)

and  adaptiveStageMass n · overlapRateBound c n ≤ 40/√(n+2).

Budget (σ := √(n+2)): T1 ≤ 3/σ, T2 ≤ 12/σ, T3 ≤ 6/σ, T4 ≤ 18/σ; 39 ≤ 40.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The s-free overlap rate (E1's bound with the δ-factors dropped). -/
def overlapRateBound (c : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * adaptiveL c n)
    + Real.pi * admR n / (2 * adaptiveL c n)
    + 1 / ((adaptiveN c n : ℝ) * (Real.pi / adaptiveL c n))
    + (1 + Real.log (adaptiveN c n)) / (2 * Real.pi * adaptiveL c n)

/-- **E3b — the gate decay rate**: mass · overlap rate ≤ 40/√(n+2). -/
theorem mass_mul_overlapRate_le (c : ℝ) (n : ℕ) :
    adaptiveStageMass n * overlapRateBound c n
      ≤ 40 / Real.sqrt ((n : ℝ) + 2) := by
  set s : ℝ := Real.sqrt ((n : ℝ) + 2) with hsdef
  set L : ℝ := adaptiveL c n with hLdef
  have hn2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
  have hs0 : (0:ℝ) < s := Real.sqrt_pos.mpr hn2
  have hss : s * s = (n : ℝ) + 2 := Real.mul_self_sqrt hn2.le
  have hncast : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hs1 : (1:ℝ) ≤ s := by nlinarith [hs0, hss, hncast]
  -- power ladder
  have hs2s : s ≤ s ^ 2 := by nlinarith [hs1, hs0]
  have hs2sq : (1:ℝ) ≤ s ^ 2 := by nlinarith [hs1, hs2s]
  have hpow3 : s ≤ s ^ 3 := by nlinarith [hs2sq, hs0]
  have hpow4 : s ≤ s ^ 4 := by nlinarith [hpow3, hs0, hs2s]
  have hpow5 : s ≤ s ^ 5 := by nlinarith [hpow4, hs0, hs2s]
  have hL8 : (8:ℝ) ≤ L := eight_le_adaptiveL c n
  have hL : (0:ℝ) < L := by linarith
  have hLs6 : s ^ 6 ≤ L := by
    have h1 : s ^ 6 = ((n : ℝ) + 2) ^ 3 := by
      have h : s ^ 6 = (s * s) ^ 3 := by ring
      rw [h, hss]
    have h2 : ((n : ℝ) + 2) ^ 3 = admL n := by unfold admL; norm_num
    rw [h1, h2]
    exact admL_le_adaptiveL c n
  have hN : (0:ℝ) < ((adaptiveN c n : ℕ) : ℝ) := by
    exact_mod_cast adaptiveN_pos c n
  have hmass0 : (0:ℝ) ≤ adaptiveStageMass n := by
    unfold adaptiveStageMass
    exact Finset.sum_nonneg fun q _ => norm_nonneg _
  have hmass : adaptiveStageMass n ≤ 6 * s := by
    have h := adaptiveStageMass_le_sqrt n
    rw [← hsdef] at h
    nlinarith [hs1]
  have hR : admR n ≤ s := by
    have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * Real.sqrt ((n : ℝ) + 2) :=
      log_le_two_sqrt hn2
    rw [← hsdef] at hlog
    have hadmR : admR n = Real.log ((n : ℝ) + 2) / 2 := by
      unfold admR; norm_num
    rw [hadmR]
    linarith
  have hR0 : (0:ℝ) ≤ admR n := by
    have hadmR : admR n = Real.log ((n : ℝ) + 2) / 2 := by
      unfold admR; norm_num
    rw [hadmR]
    have : (0:ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    linarith
  have hM_lb : Real.pi * s ^ 2
      ≤ ((adaptiveN c n : ℕ) : ℝ) * (Real.pi / L) := by
    have h1 : L * ((n : ℝ) + 2) ≤ ((adaptiveN c n : ℕ) : ℝ) := by
      rw [hLdef]
      exact adaptiveL_mul_le_adaptiveN c n
    have h2 : (L * ((n : ℝ) + 2)) * (Real.pi / L)
        ≤ ((adaptiveN c n : ℕ) : ℝ) * (Real.pi / L) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (L * ((n : ℝ) + 2)) * (Real.pi / L)
        = Real.pi * ((n : ℝ) + 2) := by
      first
        | (field_simp; ring)
        | field_simp
    have h4 : Real.pi * s ^ 2 = Real.pi * ((n : ℝ) + 2) := by
      rw [show s ^ 2 = s * s by ring, hss]
    rw [h4, ← h3]
    exact h2
  have hNle : ((adaptiveN c n : ℕ) : ℝ) ≤ 3 * L ^ 2 := by
    rw [hLdef]
    exact adaptiveN_le_three_L_sq c n
  have hsqrtL0 : (0:ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hLsqrt : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  have hsqrtL2 : (2:ℝ) ≤ Real.sqrt L := by
    nlinarith [Real.sq_sqrt hL.le, Real.sqrt_nonneg L, hL8]
  have hsqrtLs3 : s ^ 3 ≤ Real.sqrt L := by
    have h1 : Real.sqrt (s ^ 6) ≤ Real.sqrt L := Real.sqrt_le_sqrt hLs6
    have h2 : Real.sqrt (s ^ 6) = s ^ 3 := by
      rw [show s ^ 6 = (s ^ 3) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    linarith [h2 ▸ h1]
  have hlogN : Real.log ((adaptiveN c n : ℕ) : ℝ)
      ≤ 2 + 4 * Real.sqrt L := by
    have h1 : Real.log ((adaptiveN c n : ℕ) : ℝ)
        ≤ Real.log (3 * L ^ 2) := by
      first
        | exact Real.log_le_log hN hNle
        | exact Real.log_le_log_of_le hNle
        | (gcongr; exact hNle)
        | (apply Real.log_le_log_of_le hNle)
    have h2 : Real.log (3 * L ^ 2)
        = Real.log 3 + 2 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
      linarith
    have h4 : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt hL
    rw [h2] at h1
    linarith
  have h1logN : 1 + Real.log ((adaptiveN c n : ℕ) : ℝ)
      ≤ 6 * Real.sqrt L := by
    nlinarith [hlogN, hsqrtL2]
  have hlogN0 : (0:ℝ) ≤ 1 + Real.log ((adaptiveN c n : ℕ) : ℝ) := by
    have : (0:ℝ) ≤ Real.log ((adaptiveN c n : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast adaptiveN_pos c n
    linarith
  -- ==== the four terms ====
  have hT1 : adaptiveStageMass n * (1 / (2 * L)) ≤ 3 / s := by
    calc adaptiveStageMass n * (1 / (2 * L))
        ≤ (6 * s) * (1 / (2 * s ^ 6)) := by
          apply mul_le_mul hmass ?_ (by positivity) (by positivity)
          gcongr
      _ = 3 / s ^ 5 := by
          first
            | (field_simp; ring)
            | field_simp
      _ ≤ 3 / s := by
          gcongr
          all_goals exact hpow5
  have hT2 : adaptiveStageMass n * (Real.pi * admR n / (2 * L))
      ≤ 12 / s := by
    calc adaptiveStageMass n * (Real.pi * admR n / (2 * L))
        ≤ (6 * s) * (Real.pi * s / (2 * s ^ 6)) := by
          apply mul_le_mul hmass ?_ (by positivity) (by positivity)
          gcongr
          try exact Real.pi_pos.le
      _ = 3 * Real.pi / s ^ 4 := by
          first
            | (field_simp; ring)
            | field_simp
      _ ≤ 12 / s ^ 4 := by
          gcongr
          all_goals linarith [Real.pi_le_four]
      _ ≤ 12 / s := by
          gcongr
          all_goals exact hpow4
  have hT3 : adaptiveStageMass n
      * (1 / (((adaptiveN c n : ℕ) : ℝ) * (Real.pi / L))) ≤ 6 / s := by
    calc adaptiveStageMass n
          * (1 / (((adaptiveN c n : ℕ) : ℝ) * (Real.pi / L)))
        ≤ (6 * s) * (1 / (Real.pi * s ^ 2)) := by
          apply mul_le_mul hmass ?_ (by positivity) (by positivity)
          gcongr
          all_goals first | positivity | exact hM_lb
      _ = 6 / (Real.pi * s) := by
          first
            | (field_simp; ring)
            | field_simp
      _ ≤ 6 / s := by
          gcongr
          all_goals nlinarith [Real.pi_gt_three, hs0]
  have hT4 : adaptiveStageMass n
      * ((1 + Real.log ((adaptiveN c n : ℕ) : ℝ)) / (2 * Real.pi * L))
      ≤ 18 / s := by
    calc adaptiveStageMass n
          * ((1 + Real.log ((adaptiveN c n : ℕ) : ℝ)) / (2 * Real.pi * L))
        ≤ (6 * s) * ((6 * Real.sqrt L) / (2 * Real.pi * L)) := by
          apply mul_le_mul hmass ?_ (by positivity) (by positivity)
          gcongr
      _ = 18 * s / (Real.pi * Real.sqrt L) := by
          rw [show 2 * Real.pi * L
              = 2 * Real.pi * (Real.sqrt L * Real.sqrt L) by rw [hLsqrt]]
          first
            | (field_simp; ring)
            | field_simp
      _ ≤ 18 * s / (Real.pi * s ^ 3) := by
          gcongr
      _ = 18 / (Real.pi * s ^ 2) := by
          first
            | (field_simp; ring)
            | field_simp
      _ ≤ 18 / s := by
          gcongr
          all_goals nlinarith [Real.pi_gt_three, hs2s, sq_nonneg s]
  -- ==== assemble ====
  have hexpand : adaptiveStageMass n * overlapRateBound c n
      = adaptiveStageMass n * (1 / (2 * L))
        + adaptiveStageMass n * (Real.pi * admR n / (2 * L))
        + adaptiveStageMass n
            * (1 / (((adaptiveN c n : ℕ) : ℝ) * (Real.pi / L)))
        + adaptiveStageMass n
            * ((1 + Real.log ((adaptiveN c n : ℕ) : ℝ))
                / (2 * Real.pi * L)) := by
    unfold overlapRateBound
    rw [← hLdef]
    ring
  rw [hexpand]
  have heq : (3:ℝ) / s + 12 / s + 6 / s + 18 / s = 39 / s := by ring
  have h40 : (39:ℝ) / s ≤ 40 / s := by
    gcongr
    all_goals norm_num
  linarith [hT1, hT2, hT3, hT4, heq, h40]

#print axioms mass_mul_overlapRate_le

end

end RHFormalization
