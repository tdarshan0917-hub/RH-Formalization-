-- SENTINEL: E3a-v2
import RHFormalization.AdaptiveWeightedDefectSum
import Mathlib

/-!
# Growth bounds for the adaptive schedule (defect-gate E3a)

Two helpers for the overlap0 squeeze:
  log x ≤ 2√x                    (for x > 0)
  (adaptiveN c n : ℝ) ≤ 3·(adaptiveL c n)²

The second tames the (1+log N)/L rate term: log N ≤ log 3 + 2 log L
≤ 3 + 4√L, so mass·(1+log N)/L ~ √n·√L/L = √n/√L ≤ √n/(n+2)^{3/2} → 0.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- Eight is a lower bound for the adaptive box width. -/
theorem eight_le_adaptiveL (c : ℝ) (n : ℕ) :
    (8:ℝ) ≤ adaptiveL c n := by
  have h := admL_le_adaptiveL c n
  have h8 : (8:ℝ) ≤ admL n := by
    unfold admL
    have h2 : (2:ℝ) ≤ ((n:ℝ) + 2) := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    nlinarith [h2, sq_nonneg ((n:ℝ) + 2), sq_nonneg (((n:ℝ) + 2) - 2)]
  linarith

/-- `N_n ≤ 3·L_n²` (the log-taming bound). -/
theorem adaptiveN_le_three_L_sq (c : ℝ) (n : ℕ) :
    ((adaptiveN c n : ℕ) : ℝ) ≤ 3 * (adaptiveL c n) ^ 2 := by
  set L : ℝ := adaptiveL c n with hLdef
  have hL8 : (8:ℝ) ≤ L := eight_le_adaptiveL c n
  have hL : (0:ℝ) < L := by linarith
  have hn2L : ((n:ℝ) + 2) ≤ L := by
    have h := admL_le_adaptiveL c n
    have hcube : ((n:ℝ) + 2) ≤ admL n := by
      unfold admL
      have hb : (1:ℝ) ≤ (n:ℝ) + 2 := by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      nlinarith [hb, sq_nonneg ((n:ℝ) + 2), sq_nonneg (((n:ℝ) + 2) - 1)]
    linarith
  -- N = max(admN, ⌈L(n+2)⌉); bound each branch by 3L²
  have hadmN : ((admN n : ℕ) : ℝ) ≤ L ^ 2 := by
    have hcube : ((n:ℝ) + 2) ^ 3 ≤ L := by
      have h := admL_le_adaptiveL c n
      have : admL n = ((n:ℝ) + 2) ^ 3 := by unfold admL; norm_num
      linarith [this ▸ h]
    have h4 : ((admN n : ℕ) : ℝ) = ((n:ℝ) + 2) ^ 4 := by
      unfold admN
      push_cast
      ring
    rw [h4]
    have hb : (1:ℝ) ≤ (n:ℝ) + 2 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    calc ((n:ℝ) + 2) ^ 4 = (((n:ℝ) + 2) ^ 3) * ((n:ℝ) + 2) := by ring
      _ ≤ L * L := by
          apply mul_le_mul hcube hn2L (by linarith) hL.le
      _ = L ^ 2 := by ring
  have hceil : ((⌈adaptiveL c n * ((n:ℝ) + 2)⌉₊ : ℕ) : ℝ)
      ≤ 2 * L ^ 2 := by
    have h1 : ((⌈adaptiveL c n * ((n:ℝ) + 2)⌉₊ : ℕ) : ℝ)
        ≤ adaptiveL c n * ((n:ℝ) + 2) + 1 := by
      have := Nat.ceil_lt_add_one
        (by positivity : (0:ℝ) ≤ adaptiveL c n * ((n:ℝ) + 2))
      linarith
    calc ((⌈adaptiveL c n * ((n:ℝ) + 2)⌉₊ : ℕ) : ℝ)
        ≤ adaptiveL c n * ((n:ℝ) + 2) + 1 := h1
      _ ≤ L * L + 1 := by
          rw [← hLdef]
          have := mul_le_mul_of_nonneg_left hn2L hL.le
          linarith
      _ ≤ 2 * L ^ 2 := by nlinarith
  -- combine over the max
  have hNdef : (adaptiveN c n : ℕ)
      = max (admN n) ⌈adaptiveL c n * ((n:ℝ) + 2)⌉₊ := by
    first
      | rfl
      | (unfold adaptiveN; rfl)
      | (unfold adaptiveN; norm_num)
  rw [hNdef]
  rcases max_cases (admN n) ⌈adaptiveL c n * ((n:ℝ) + 2)⌉₊ with
    ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq]
  · nlinarith [hadmN, sq_nonneg L]
  · nlinarith [hceil, sq_nonneg L]

#print axioms eight_le_adaptiveL
#print axioms adaptiveN_le_three_L_sq

end

end RHFormalization
