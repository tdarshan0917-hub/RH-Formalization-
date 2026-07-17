-- SENTINEL: L3a-stage-bound-uniform-v4
import RHFormalization.AdaptiveDefectStageBound
import Mathlib

/-!
# L3a — Uniform-in-n domination of the stage bound
`stageBound_uniform`: mass(n)·perSpikeBound(...) ≤ 5/c₀ + 1/c₀² for all n.
v2: use the repo's existing log_le_two_sqrt; gcongr self-closes; div_le_div_iff₀
(₀-renaming family); explicit ring distribution before the final linarith.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- Mass is at most linear: `adaptiveStageMass n ≤ 4(n+2)`. -/
theorem adaptiveStageMass_le_linear (n : ℕ) :
    adaptiveStageMass n ≤ 4 * ((n : ℝ) + 2) := by
  have h := adaptiveStageMass_le_sqrt n
  have hx2 : (2:ℝ) ≤ (n : ℝ) + 2 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsq : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
    have h1 : Real.sqrt ((n : ℝ) + 2) ≤ Real.sqrt (((n : ℝ) + 2)^2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h1
  linarith

/-- `1 + log N ≤ 6√L` at the live schedule (N ≤ 3L², L ≥ 8). -/
theorem one_add_log_adaptiveN_le (c : ℝ) (n : ℕ) :
    1 + Real.log ((adaptiveN c n : ℕ) : ℝ)
      ≤ 6 * Real.sqrt (adaptiveL c n) := by
  set L : ℝ := adaptiveL c n with hLdef
  have hL0 : (0:ℝ) < L := adaptiveL_pos c n
  have hL8 : (8:ℝ) ≤ L := eight_le_adaptiveL c n
  have hN0' : (0:ℝ) < ((adaptiveN c n : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (adaptiveN_pos c n)
  have hNle : ((adaptiveN c n : ℕ) : ℝ) ≤ 3 * L^2 := adaptiveN_le_three_L_sq c n
  have hlog1 : Real.log ((adaptiveN c n : ℕ) : ℝ) ≤ Real.log (3 * L^2) := by
    gcongr
  have hlog2 : Real.log (3 * L^2) = Real.log 3 + 2 * Real.log L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    linarith
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt hL0
  have hsL : (2:ℝ) ≤ Real.sqrt L := by
    have h4 : (2:ℝ)^2 ≤ L := by nlinarith
    have h1 : Real.sqrt ((2:ℝ)^2) ≤ Real.sqrt L := Real.sqrt_le_sqrt h4
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h1
  linarith [hlog1, hlog2, hlog3, hlogL, hsL]

set_option maxHeartbeats 800000 in
/-- **L3a — the uniform stage bound**: independent of n. -/
theorem stageBound_uniform (c : ℝ) (n : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    adaptiveStageMass n
        * perSpikeBound (admR n) (adaptiveL c n) (adaptiveN c n) c₀
      ≤ 5 / c₀ + 1 / c₀^2 := by
  set x : ℝ := (n : ℝ) + 2 with hxdef
  set L : ℝ := adaptiveL c n with hLdef
  have hx2 : (2:ℝ) ≤ x := by
    rw [hxdef]
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hx0 : (0:ℝ) < x := by linarith
  have hL0 : (0:ℝ) < L := adaptiveL_pos c n
  have hL8 : (8:ℝ) ≤ L := eight_le_adaptiveL c n
  have hLx3 : x^3 ≤ L := by
    have h := admL_le_adaptiveL c n
    unfold admL at h
    rw [← hxdef] at h
    exact h
  have hN0' : (0:ℝ) < ((adaptiveN c n : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (adaptiveN_pos c n)
  have hNx : L * x ≤ ((adaptiveN c n : ℕ) : ℝ) := by
    have h := adaptiveL_mul_le_adaptiveN c n
    rw [← hxdef] at h
    exact h
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  have hR : admR n ≤ x / 2 := by
    unfold admR
    rw [← hxdef]
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < x by linarith)
    linarith
  have hR0 : (0:ℝ) ≤ admR n := by
    unfold admR
    rw [← hxdef]
    have h1 : (1:ℝ) ≤ x := by linarith
    have := Real.log_nonneg h1
    linarith
  have hlogN0 : (0:ℝ) ≤ Real.log ((adaptiveN c n : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast adaptiveN_pos c n
  have hmass := adaptiveStageMass_le_linear n
  rw [← hxdef] at hmass
  have hmass0 : (0:ℝ) ≤ adaptiveStageMass n := by
    unfold adaptiveStageMass
    exact Finset.sum_nonneg fun q _ => norm_nonneg _
  -- √ ladder
  have hsqL_ge : x * Real.sqrt x ≤ Real.sqrt L := by
    have h1 : Real.sqrt (x^3) ≤ Real.sqrt L := Real.sqrt_le_sqrt hLx3
    have h2 : Real.sqrt (x^3) = x * Real.sqrt x := by
      rw [show x^3 = x^2 * x by ring, Real.sqrt_mul (sq_nonneg x) x,
        Real.sqrt_sq hx0.le]
    rw [← h2]
    exact h1
  have h14 : (1.4:ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1.4:ℝ)^2 ≤ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.4)] at h
  have hA2 : (1.4:ℝ) ≤ Real.sqrt x := le_trans h14 (Real.sqrt_le_sqrt hx2)
  have hA3 : (1.4:ℝ) * x ≤ Real.sqrt L := by
    have h1 : (1.4:ℝ) * x ≤ Real.sqrt x * x :=
      mul_le_mul_of_nonneg_right hA2 hx0.le
    nlinarith [hsqL_ge]
  have hstep1 : 4 * x ≤ Real.pi * Real.sqrt L := by
    have h1 : Real.pi * ((1.4:ℝ) * x) ≤ Real.pi * Real.sqrt L :=
      mul_le_mul_of_nonneg_left hA3 hπ.le
    nlinarith [h1, mul_nonneg (by linarith : (0:ℝ) ≤ Real.pi - 3) hx0.le]
  have hLs : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  -- Term 1
  have hA4 : 4 * x * ((1 / (2 * L)) * ((admR n / c₀) * (Real.pi / 2) + 1 / c₀^2))
      ≤ 1 / c₀ + 1 / c₀^2 := by
    have hsingle : 4 * x * ((1 / (2 * L)) * ((admR n / c₀) * (Real.pi / 2) + 1 / c₀^2))
        = (2 * x * admR n * Real.pi * c₀ + 4 * x) / (2 * L * c₀^2) := by
      field_simp
      ring
    have hRHS : 1 / c₀ + 1 / c₀^2 = (2 * L * c₀ + 2 * L) / (2 * L * c₀^2) := by
      field_simp
    rw [hsingle, hRHS]
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    have k1 : 2 * x * admR n * Real.pi ≤ 2 * L := by
      nlinarith [hR, hR0, hLx3, hx2, hπ4, hπ.le,
        mul_nonneg (mul_nonneg hx0.le hπ.le) (by linarith : (0:ℝ) ≤ x/2 - admR n),
        mul_nonneg (sq_nonneg x) (by linarith : (0:ℝ) ≤ 4 - Real.pi),
        mul_nonneg (sq_nonneg x) (by linarith : (0:ℝ) ≤ x - 2)]
    have k2 : 4 * x ≤ 2 * L := by nlinarith [hLx3, hx2]
    have k1' := mul_le_mul_of_nonneg_right k1 hc₀.le
    linarith [k1', k2]
  -- Term 2
  have hB4 : 4 * x * (L / (2 * c₀ * Real.pi^2 * ((adaptiveN c n : ℕ) : ℝ)))
      ≤ 1 / c₀ := by
    have hsB : 4 * x * (L / (2 * c₀ * Real.pi^2 * ((adaptiveN c n : ℕ) : ℝ)))
        = (4 * x * L) / (2 * c₀ * Real.pi^2 * ((adaptiveN c n : ℕ) : ℝ)) := by
      ring
    rw [hsB, div_le_div_iff₀ (by positivity) hc₀]
    have hπ2 : (9:ℝ) ≤ Real.pi^2 := by nlinarith [hπ3]
    have key1 : 4 * x * L * c₀ ≤ 2 * c₀ * Real.pi^2 * (L * x) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.pi^2 - 9)
        (mul_nonneg (mul_nonneg hL0.le hx0.le) hc₀.le),
        mul_nonneg (mul_nonneg hL0.le hx0.le) hc₀.le]
    have key2 : 2 * c₀ * Real.pi^2 * (L * x)
        ≤ 2 * c₀ * Real.pi^2 * ((adaptiveN c n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hNx (by positivity)
    linarith [key1, key2]
  -- Term 3
  have h6 := one_add_log_adaptiveN_le c n
  rw [← hLdef] at h6
  have hC4 : 4 * x * ((1 / (2 * L * c₀ * Real.pi))
        * (1 + Real.log ((adaptiveN c n : ℕ) : ℝ)))
      ≤ 3 / c₀ := by
    have hsC : 4 * x * ((1 / (2 * L * c₀ * Real.pi))
          * (1 + Real.log ((adaptiveN c n : ℕ) : ℝ)))
        = (4 * x * (1 + Real.log ((adaptiveN c n : ℕ) : ℝ)))
            / (2 * L * c₀ * Real.pi) := by
      ring
    rw [hsC, div_le_div_iff₀ (by positivity) hc₀]
    have t1 : 4 * x * (1 + Real.log ((adaptiveN c n : ℕ) : ℝ)) * c₀
        ≤ 24 * (x * Real.sqrt L * c₀) := by
      have h := mul_le_mul_of_nonneg_left h6
        (show (0:ℝ) ≤ 4 * x * c₀ by positivity)
      linarith [h]
    have t2 : 4 * (x * Real.sqrt L * c₀) ≤ Real.pi * L * c₀ := by
      have h := mul_le_mul_of_nonneg_right hstep1
        (mul_nonneg (Real.sqrt_nonneg L) hc₀.le)
      calc 4 * (x * Real.sqrt L * c₀) = 4 * x * (Real.sqrt L * c₀) := by ring
        _ ≤ Real.pi * Real.sqrt L * (Real.sqrt L * c₀) := h
        _ = Real.pi * (Real.sqrt L * Real.sqrt L) * c₀ := by ring
        _ = Real.pi * L * c₀ := by rw [hLs]
    linarith [t1, t2]
  -- perSpikeBound nonneg + assembly
  have hPSB0 : (0:ℝ) ≤ perSpikeBound (admR n) L (adaptiveN c n) c₀ := by
    unfold perSpikeBound
    have t1 : (0:ℝ) ≤ (1 / (2 * L)) * ((admR n / c₀) * (Real.pi / 2) + 1 / c₀^2) := by
      apply mul_nonneg (by positivity)
      apply add_nonneg
      · exact mul_nonneg (div_nonneg hR0 hc₀.le) (by positivity)
      · positivity
    have t2 : (0:ℝ) ≤ L / (2 * c₀ * Real.pi^2 * ((adaptiveN c n : ℕ) : ℝ)) := by
      positivity
    have t3 : (0:ℝ) ≤ (1 / (2 * L * c₀ * Real.pi))
        * (1 + Real.log ((adaptiveN c n : ℕ) : ℝ)) := by
      apply mul_nonneg (by positivity)
      linarith
    linarith
  calc adaptiveStageMass n * perSpikeBound (admR n) L (adaptiveN c n) c₀
      ≤ (4 * x) * perSpikeBound (admR n) L (adaptiveN c n) c₀ :=
        mul_le_mul_of_nonneg_right hmass hPSB0
    _ ≤ 5 / c₀ + 1 / c₀^2 := by
        unfold perSpikeBound
        have hdist : (4 * x) * ((1 / (2 * L)) * ((admR n / c₀) * (Real.pi / 2) + 1 / c₀^2)
              + L / (2 * c₀ * Real.pi^2 * ((adaptiveN c n : ℕ) : ℝ))
              + (1 / (2 * L * c₀ * Real.pi))
                  * (1 + Real.log ((adaptiveN c n : ℕ) : ℝ)))
            = 4 * x * ((1 / (2 * L)) * ((admR n / c₀) * (Real.pi / 2) + 1 / c₀^2))
              + 4 * x * (L / (2 * c₀ * Real.pi^2 * ((adaptiveN c n : ℕ) : ℝ)))
              + 4 * x * ((1 / (2 * L * c₀ * Real.pi))
                  * (1 + Real.log ((adaptiveN c n : ℕ) : ℝ))) := by ring
        rw [hdist]
        exact (add_le_add (add_le_add hA4 hB4) hC4).trans (le_of_eq (by ring))

#print axioms adaptiveStageMass_le_linear
#print axioms one_add_log_adaptiveN_le
#print axioms stageBound_uniform

end

end RHFormalization
