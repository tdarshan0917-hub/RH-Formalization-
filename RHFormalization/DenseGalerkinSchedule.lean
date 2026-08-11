/-
DENSE SCHEDULE — Brick D1 (Stage A GO, GPT-countersigned 2026-08-10).
Pilot: X_n = √(n+2), denseL = max{8, admR+1, (n+2)^(3/8)}, denseN = admN = (n+2)^4.
This file: schedule definitions + elementary floors ONLY. No stage seq yet,
no defect, no window, no Q^V, no sector assembly. Old files untouched.
Note (n+2)^(3/8) = X_n^(3/4) since X_n = (n+2)^(1/2).
-/

import RHFormalization.AdaptiveGalerkinStage

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

/-- The dense window: `max {8, admR n + 1, (n+2)^(3/8)}`. The last entry
is `X_n^(3/4)` in the `X_n = √(n+2)` coordinate. -/
def denseL (n : ℕ) : ℝ :=
  max 8 (max (admR n + 1) (((n : ℝ) + 2) ^ ((3 : ℝ) / 8)))

/-- The dense resolution: unchanged from the admissible schedule,
`denseN n = admN n = (n+2)^4 = X_n^8`. -/
def denseN (n : ℕ) : ℕ := admN n

theorem eight_le_denseL (n : ℕ) : (8 : ℝ) ≤ denseL n :=
  le_max_left _ _

theorem denseL_pos (n : ℕ) : (0 : ℝ) < denseL n :=
  lt_of_lt_of_le (by norm_num) (eight_le_denseL n)

theorem denseL_ge_one (n : ℕ) : (1 : ℝ) ≤ denseL n :=
  le_trans (by norm_num) (eight_le_denseL n)

theorem admR_add_one_le_denseL (n : ℕ) : admR n + 1 ≤ denseL n :=
  le_max_of_le_right (le_max_left _ _)

theorem rpow_le_denseL (n : ℕ) :
    ((n : ℝ) + 2) ^ ((3 : ℝ) / 8) ≤ denseL n :=
  le_max_of_le_right (le_max_right _ _)

theorem admR_lt_denseL (n : ℕ) : admR n < denseL n :=
  lt_of_lt_of_le (lt_add_one _) (admR_add_one_le_denseL n)

/-- Every active prime-power center lies (strictly inside) the dense window. -/
theorem center_le_denseL (n : ℕ) (q : PrimePowerPair)
    (hq : q ∈ activePrimePowerPairsCenterBelow (admR n)) :
    q.center ≤ denseL n := by
  rw [activePrimePowerPairsCenterBelow_mem] at hq
  exact le_trans hq.2 (admR_lt_denseL n).le

theorem denseN_cast (n : ℕ) : ((denseN n : ℕ) : ℝ) = ((n : ℝ) + 2) ^ 4 := by
  show ((admN n : ℕ) : ℝ) = ((n : ℝ) + 2) ^ 4
  first
    | (unfold admN; push_cast; ring)
    | (simp [admN]; push_cast; ring)
    | (unfold denseN admN; push_cast; ring)

theorem denseN_pos (n : ℕ) : 0 < denseN n := by
  rcases Nat.eq_zero_or_pos (denseN n) with h0 | hpos
  · exfalso
    have hc := denseN_cast n
    rw [h0] at hc
    push_cast at hc
    have hp : (0 : ℝ) < ((n : ℝ) + 2) ^ 4 := by positivity
    linarith
  · exact hpos

/-- Auxiliary: `n+2 ≤ (n+2)^3`. -/
theorem base_le_cube (n : ℕ) : (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 3 := by
  have hx : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ)+2)
      (by linarith : (0:ℝ) ≤ (n:ℝ)+2-1)) (by linarith : (0:ℝ) ≤ (n:ℝ)+2+1)]

/-- The dense window is dominated by the cube: `denseL n ≤ (n+2)^3`.
(All three max-entries sit below the cube.) -/
theorem denseL_le_cube (n : ℕ) : denseL n ≤ ((n : ℝ) + 2) ^ 3 := by
  have hx : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hxpos : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hcube8 : (8 : ℝ) ≤ ((n : ℝ) + 2) ^ 3 := by
    nlinarith [hx, sq_nonneg ((n:ℝ)+2-2), sq_nonneg ((n:ℝ)+2),
      mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg ((n:ℝ)+2-2))]
  have hx3 := base_le_cube n
  apply max_le hcube8
  apply max_le
  · -- admR n + 1 ≤ (n+2)^3 via log x ≤ x − 1
    have hlog : Real.log ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) - 1 :=
      Real.log_le_sub_one_of_pos hxpos
    have hadmR : admR n = Real.log ((n : ℝ) + 2) / 2 := by
      first | rfl | (unfold admR; ring) | (unfold admR; push_cast; ring)
    rw [hadmR]
    linarith
  · -- (n+2)^(3/8) ≤ (n+2)^1 ≤ (n+2)^3
    have h1 : ((n : ℝ) + 2) ^ ((3 : ℝ) / 8) ≤ ((n : ℝ) + 2) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      norm_num
    rw [Real.rpow_one] at h1
    linarith

/-- **Dense resolution comparison**: `denseL n * (n+2) ≤ denseN n`.
The dense analogue of the load-bearing density ratio, with slack `X^(21/4)`. -/
theorem denseL_mul_le_denseN (n : ℕ) :
    denseL n * ((n : ℝ) + 2) ≤ ((denseN n : ℕ) : ℝ) := by
  have hxpos : (0 : ℝ) < (n : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  rw [denseN_cast]
  calc denseL n * ((n : ℝ) + 2)
      ≤ ((n : ℝ) + 2) ^ 3 * ((n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right (denseL_le_cube n) hxpos.le
    _ = ((n : ℝ) + 2) ^ 4 := by ring

/-- Coordinate bridge: `X_n^(3/4) ≤ denseL n` in the `X_n = exp(admR n)` form. -/
theorem exp_admR_rpow_le_denseL (n : ℕ) :
    (Real.exp (admR n)) ^ ((3 : ℝ) / 4) ≤ denseL n := by
  have hxpos : (0 : ℝ) < (n : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hadmR : admR n = Real.log ((n : ℝ) + 2) / 2 := by
    first | rfl | (unfold admR; ring)
  have hexp : Real.exp (admR n) = ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
    rw [hadmR, Real.rpow_def_of_pos hxpos]
    ring_nf
  have key : (Real.exp (admR n)) ^ ((3 : ℝ) / 4)
      = ((n : ℝ) + 2) ^ ((3 : ℝ) / 8) := by
    rw [hexp, ← Real.rpow_mul hxpos.le]
    first
      | norm_num
      | (congr 1; norm_num)
      | (congr 1; ring)
  rw [key]
  exact rpow_le_denseL n

#print axioms denseL_pos
#print axioms eight_le_denseL
#print axioms admR_add_one_le_denseL
#print axioms center_le_denseL
#print axioms denseN_cast
#print axioms denseN_pos
#print axioms denseL_le_cube
#print axioms denseL_mul_le_denseN
#print axioms exp_admR_rpow_le_denseL

end

end RHFormalization
