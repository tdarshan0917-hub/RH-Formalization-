/-
DENSE SCHEDULE — Brick D4a: the dense uniform stage bound (Lemma 2 arithmetic).
`adaptiveStageMass n · perSpikeBound (admR n) (denseL n) (denseN n) c₀
   ≤ 115B/c₀ + 6B/c₀²`, B = log4+4.
Replaces `stageBound_uniform`'s giant-schedule proof ((n+2)³ ≤ L, N ≤ 3L²)
with: sharp mass (D3c), denseL ≥ x^{3/8} (D1), denseL ≤ x³ (D1), denseN = x⁴
(D1), log x ≤ 8x^{1/8}. Mass is schedule-blind (depends only on admR n).
-/

import RHFormalization.DenseGalerkinSchedule
import RHFormalization.DenseSharpMassSchedule
import RHFormalization.AdaptiveDefectStageBound

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Real

theorem one_le_rpow_eighth {x : ℝ} (hx1 : 1 ≤ x) : (1:ℝ) ≤ x ^ ((1:ℝ)/8) := by
  have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1
    (by norm_num : (0:ℝ) ≤ (1:ℝ)/8)
  rwa [Real.one_rpow] at h

theorem log_le_eight_rpow_eighth {x : ℝ} (hx1 : 1 ≤ x) :
    Real.log x ≤ 8 * x ^ ((1:ℝ)/8) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hp : (0:ℝ) < x ^ ((1:ℝ)/8) := Real.rpow_pos_of_pos hx0 _
  have h := Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow hx0] at h
  linarith

theorem sqrt_exp_admR_eq_rpow_quarter (n : ℕ) :
    Real.sqrt (Real.exp (admR n)) = ((n:ℝ)+2) ^ ((1:ℝ)/4) := by
  have hx0 : (0:ℝ) ≤ (n:ℝ)+2 := by positivity
  rw [exp_admR_eq_sqrt, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx0]
  norm_num

/-- **D4a — the dense uniform stage bound.** -/
theorem denseStageBound_uniform (n : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    adaptiveStageMass n * perSpikeBound (admR n) (denseL n) (denseN n) c₀
      ≤ 115 * (Real.log 4 + 4) / c₀ + 6 * (Real.log 4 + 4) / c₀ ^ 2 := by
  have hx2 : (2:ℝ) ≤ (n:ℝ)+2 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hx0 : (0:ℝ) < (n:ℝ)+2 := by linarith
  have hx1 : (1:ℝ) ≤ (n:ℝ)+2 := by linarith
  have hBnn : (0:ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have hLlow : ((n:ℝ)+2) ^ ((3:ℝ)/8) ≤ denseL n := rpow_le_denseL n
  have hLcube : denseL n ≤ ((n:ℝ)+2)^3 := denseL_le_cube n
  have hN : ((denseN n : ℕ) : ℝ) = ((n:ℝ)+2)^4 := denseN_cast n
  have hN0 : (0:ℝ) < ((denseN n : ℕ) : ℝ) := by rw [hN]; positivity
  have hmass : adaptiveStageMass n
      ≤ 12 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((1:ℝ)/4) := by
    have h := adaptiveStageMass_le_sqrt_exp n
    rwa [sqrt_exp_admR_eq_rpow_quarter n] at h
  have hmass0 : (0:ℝ) ≤ adaptiveStageMass n := by
    unfold adaptiveStageMass
    exact Finset.sum_nonneg fun q _ => norm_nonneg _
  have hR_eq : admR n = Real.log ((n:ℝ)+2) / 2 := by
    first | rfl | (unfold admR; ring) | (unfold admR; push_cast; ring)
  have hR0 : (0:ℝ) ≤ admR n := by
    rw [hR_eq]
    have := Real.log_nonneg hx1
    linarith
  have hlogx : Real.log ((n:ℝ)+2) ≤ 8 * ((n:ℝ)+2) ^ ((1:ℝ)/8) :=
    log_le_eight_rpow_eighth hx1
  have hx8_1 : (1:ℝ) ≤ ((n:ℝ)+2) ^ ((1:ℝ)/8) := one_le_rpow_eighth hx1
  have hx8_0 : (0:ℝ) ≤ ((n:ℝ)+2) ^ ((1:ℝ)/8) := by linarith
  have hx4_0 : (0:ℝ) ≤ ((n:ℝ)+2) ^ ((1:ℝ)/4) := (Real.rpow_pos_of_pos hx0 _).le
  have hmul1 : ((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2) ^ ((1:ℝ)/8)
      = ((n:ℝ)+2) ^ ((3:ℝ)/8) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hle_q38 : ((n:ℝ)+2) ^ ((1:ℝ)/4) ≤ ((n:ℝ)+2) ^ ((3:ℝ)/8) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hle134 : ((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2)^3 ≤ ((denseN n : ℕ) : ℝ) := by
    have h1 : ((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2)^3 = ((n:ℝ)+2) ^ ((13:ℝ)/4) := by
      rw [show ((n:ℝ)+2)^3 = ((n:ℝ)+2) ^ ((3:ℕ):ℝ) by rw [Real.rpow_natCast],
        ← Real.rpow_add hx0]
      norm_num
    have h3 : ((n:ℝ)+2) ^ ((4:ℝ)) = ((n:ℝ)+2)^4 := by
      rw [show ((4:ℝ)) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [h1, hN, ← h3]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hlogN : Real.log ((denseN n : ℕ) : ℝ) = 4 * Real.log ((n:ℝ)+2) := by
    rw [hN, Real.log_pow]
    push_cast
    ring
  -- key product bounds
  have hmassR : adaptiveStageMass n * admR n
      ≤ 48 * (Real.log 4 + 4) * denseL n := by
    have hRle : admR n ≤ 4 * ((n:ℝ)+2) ^ ((1:ℝ)/8) := by
      rw [hR_eq]; linarith
    calc adaptiveStageMass n * admR n
        ≤ (12 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((1:ℝ)/4))
            * (4 * ((n:ℝ)+2) ^ ((1:ℝ)/8)) := by
          apply mul_le_mul hmass hRle hR0 (by nlinarith)
      _ = 48 * (Real.log 4 + 4)
            * (((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2) ^ ((1:ℝ)/8)) := by ring
      _ = 48 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((3:ℝ)/8) := by rw [hmul1]
      _ ≤ 48 * (Real.log 4 + 4) * denseL n := by nlinarith [hLlow, hBnn]
  have hmassle : adaptiveStageMass n ≤ 12 * (Real.log 4 + 4) * denseL n := by
    calc adaptiveStageMass n
        ≤ 12 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((1:ℝ)/4) := hmass
      _ ≤ 12 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((3:ℝ)/8) := by nlinarith [hle_q38, hBnn]
      _ ≤ 12 * (Real.log 4 + 4) * denseL n := by nlinarith [hLlow, hBnn]
  have hmassLN : adaptiveStageMass n * denseL n
      ≤ 12 * (Real.log 4 + 4) * ((denseN n : ℕ) : ℝ) := by
    calc adaptiveStageMass n * denseL n
        ≤ (12 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((1:ℝ)/4)) * (((n:ℝ)+2)^3) := by
          apply mul_le_mul hmass hLcube hL0.le (by nlinarith)
      _ = 12 * (Real.log 4 + 4) * (((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2)^3) := by ring
      _ ≤ 12 * (Real.log 4 + 4) * ((denseN n : ℕ) : ℝ) := by nlinarith [hle134, hBnn]
  have hmasslogN : adaptiveStageMass n * (1 + Real.log ((denseN n : ℕ) : ℝ))
      ≤ 396 * (Real.log 4 + 4) * denseL n := by
    have h1 : 1 + Real.log ((denseN n : ℕ) : ℝ) ≤ 33 * ((n:ℝ)+2) ^ ((1:ℝ)/8) := by
      rw [hlogN]
      nlinarith [hlogx, hx8_1]
    have h0 : (0:ℝ) ≤ 1 + Real.log ((denseN n : ℕ) : ℝ) := by
      rw [hlogN]
      have := Real.log_nonneg hx1
      linarith
    calc adaptiveStageMass n * (1 + Real.log ((denseN n : ℕ) : ℝ))
        ≤ (12 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((1:ℝ)/4))
            * (33 * ((n:ℝ)+2) ^ ((1:ℝ)/8)) := by
          apply mul_le_mul hmass h1 h0 (by nlinarith)
      _ = 396 * (Real.log 4 + 4)
            * (((n:ℝ)+2) ^ ((1:ℝ)/4) * ((n:ℝ)+2) ^ ((1:ℝ)/8)) := by ring
      _ = 396 * (Real.log 4 + 4) * ((n:ℝ)+2) ^ ((3:ℝ)/8) := by rw [hmul1]
      _ ≤ 396 * (Real.log 4 + 4) * denseL n := by nlinarith [hLlow, hBnn]
  -- expand and bound the four pieces
  have hπ0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  have hπ9 : (9:ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hexpand : adaptiveStageMass n
        * perSpikeBound (admR n) (denseL n) (denseN n) c₀
      = adaptiveStageMass n * admR n * Real.pi / (4 * denseL n * c₀)
        + adaptiveStageMass n / (2 * denseL n * c₀^2)
        + adaptiveStageMass n * denseL n
            / (2 * c₀ * Real.pi^2 * ((denseN n : ℕ) : ℝ))
        + adaptiveStageMass n * (1 + Real.log ((denseN n : ℕ) : ℝ))
            / (2 * denseL n * c₀ * Real.pi) := by
    unfold perSpikeBound
    first | ring | (field_simp; ring)
  have hA : adaptiveStageMass n * admR n * Real.pi / (4 * denseL n * c₀)
      ≤ 48 * (Real.log 4 + 4) / c₀ := by
    have hnum : adaptiveStageMass n * admR n * Real.pi
        ≤ 192 * (Real.log 4 + 4) * denseL n := by
      have h1 : adaptiveStageMass n * admR n * Real.pi
          ≤ (48 * (Real.log 4 + 4) * denseL n) * Real.pi :=
        mul_le_mul_of_nonneg_right hmassR hπ0.le
      have h2 : (48 * (Real.log 4 + 4) * denseL n) * Real.pi
          ≤ (48 * (Real.log 4 + 4) * denseL n) * 4 := by
        apply mul_le_mul_of_nonneg_left hπ4
        nlinarith [hBnn, hL0.le, mul_nonneg hBnn hL0.le]
      calc adaptiveStageMass n * admR n * Real.pi
          ≤ (48 * (Real.log 4 + 4) * denseL n) * Real.pi := h1
        _ ≤ (48 * (Real.log 4 + 4) * denseL n) * 4 := h2
        _ = 192 * (Real.log 4 + 4) * denseL n := by ring
    have hden : (0:ℝ) < 4 * denseL n * c₀ :=
      mul_pos (mul_pos (by norm_num) hL0) hc₀
    rw [div_le_iff₀ hden]
    have hEq : 48 * (Real.log 4 + 4) / c₀ * (4 * denseL n * c₀)
        = 192 * (Real.log 4 + 4) * denseL n := by
      field_simp
      try ring
    rw [hEq]
    exact hnum
  have hB2 : adaptiveStageMass n / (2 * denseL n * c₀^2)
      ≤ 6 * (Real.log 4 + 4) / c₀ ^ 2 := by
    have hden : (0:ℝ) < 2 * denseL n * c₀^2 :=
      mul_pos (mul_pos (by norm_num) hL0) (pow_pos hc₀ 2)
    rw [div_le_iff₀ hden]
    have hEq : 6 * (Real.log 4 + 4) / c₀ ^ 2 * (2 * denseL n * c₀^2)
        = 12 * (Real.log 4 + 4) * denseL n := by
      field_simp
      try ring
    rw [hEq]
    exact hmassle
  have hC : adaptiveStageMass n * denseL n
        / (2 * c₀ * Real.pi^2 * ((denseN n : ℕ) : ℝ))
      ≤ (Real.log 4 + 4) / c₀ := by
    have hπ2 : (0:ℝ) < Real.pi^2 := pow_pos hπ0 2
    have hden : (0:ℝ) < 2 * c₀ * Real.pi^2 * ((denseN n : ℕ) : ℝ) :=
      mul_pos (mul_pos (mul_pos (by norm_num) hc₀) hπ2) hN0
    rw [div_le_iff₀ hden]
    have hEq : (Real.log 4 + 4) / c₀ * (2 * c₀ * Real.pi^2 * ((denseN n : ℕ) : ℝ))
        = 2 * (Real.log 4 + 4) * Real.pi^2 * ((denseN n : ℕ) : ℝ) := by
      field_simp
      try ring
    rw [hEq]
    have hkey : 12 * (Real.log 4 + 4) * ((denseN n : ℕ) : ℝ)
        ≤ 2 * (Real.log 4 + 4) * Real.pi^2 * ((denseN n : ℕ) : ℝ) := by
      nlinarith [mul_nonneg hBnn hN0.le,
        mul_nonneg (mul_nonneg hBnn hN0.le) (sub_nonneg.mpr hπ9)]
    linarith [hmassLN, hkey]
  have hD : adaptiveStageMass n * (1 + Real.log ((denseN n : ℕ) : ℝ))
        / (2 * denseL n * c₀ * Real.pi)
      ≤ 66 * (Real.log 4 + 4) / c₀ := by
    have hden : (0:ℝ) < 2 * denseL n * c₀ * Real.pi :=
      mul_pos (mul_pos (mul_pos (by norm_num) hL0) hc₀) hπ0
    rw [div_le_iff₀ hden]
    have hEq : 66 * (Real.log 4 + 4) / c₀ * (2 * denseL n * c₀ * Real.pi)
        = 132 * (Real.log 4 + 4) * denseL n * Real.pi := by
      field_simp
      try ring
    rw [hEq]
    have hkey : 396 * (Real.log 4 + 4) * denseL n
        ≤ 132 * (Real.log 4 + 4) * denseL n * Real.pi := by
      nlinarith [mul_nonneg hBnn hL0.le,
        mul_nonneg (mul_nonneg hBnn hL0.le) (sub_nonneg.mpr hπ3)]
    linarith [hmasslogN, hkey]
  rw [hexpand]
  refine le_trans
    (add_le_add (add_le_add (add_le_add hA hB2) hC) hD) (le_of_eq ?_)
  try ring
  try norm_num
  try rfl

#print axioms denseStageBound_uniform

end

end RHFormalization
