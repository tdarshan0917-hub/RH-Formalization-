/-
DENSE SCHEDULE — Brick D3c: sharp mass AT THE SCHEDULE (Lemma 1 closed).
`S1mass (admR n) ≤ 12(log4+4)·√X_n` with `X_n = e^{admR n} = √(n+2)`.
K-choice: K = Nat.log 2 ⌈√(n+2)⌉₊, giving √(n+2) ≤ 2^{K+1} ≤ 4√(n+2).
One power of √ sharper than the banked `S1mass_admR_le_sqrt` (≤ 2(√(n+2)+2)):
this is O(√X_n), that was O(X_n). The input D4 (dense defect) and D5
(dense window) consume.
-/

import RHFormalization.DenseSharpMass
import RHFormalization.AdmissibleS1MassSqrt

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open Real

/-- **D3c — Lemma 1 closed: sharp mass at the schedule.** -/
theorem S1mass_admR_le_sqrt_exp (n : ℕ) :
    S1mass (admR n)
      ≤ 12 * (Real.log 4 + 4) * Real.sqrt (Real.exp (admR n)) := by
  classical
  have hx2 : (2:ℝ) ≤ (n:ℝ) + 2 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hxpos : (0:ℝ) < (n:ℝ) + 2 := by linarith
  have hsq1 : (1:ℝ) ≤ Real.sqrt ((n:ℝ) + 2) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hexp : Real.exp (admR n) = Real.sqrt ((n:ℝ) + 2) := exp_admR_eq_sqrt n
  -- the ceiling of √(n+2) and its dyadic bracket
  set m : ℕ := ⌈Real.sqrt ((n:ℝ) + 2)⌉₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  set K : ℕ := Nat.log 2 m with hK
  -- upper bracket: m < 2^(K+1), so √(n+2) ≤ m ≤ 2^(K+1)
  have hup : m < 2 ^ (K + 1) := by
    rw [hK]
    exact Nat.lt_pow_succ_log_self (by norm_num) m
  have hRK : Real.exp (admR n) ≤ (2:ℝ) ^ (K + 1) := by
    rw [hexp]
    calc Real.sqrt ((n:ℝ) + 2) ≤ (m : ℝ) := Nat.le_ceil _
      _ ≤ ((2:ℕ) ^ (K+1) : ℕ) := by exact_mod_cast hup.le
      _ = (2:ℝ) ^ (K+1) := by push_cast; ring
  -- lower bracket: 2^K ≤ m, so 2^(K+1) ≤ 2m ≤ 2(√(n+2)+1) ≤ 4√(n+2)
  have hlow : (2:ℕ) ^ K ≤ m := by
    rw [hK]
    exact Nat.pow_log_le_self 2 (by omega)
  have hceil_le : (m : ℝ) ≤ Real.sqrt ((n:ℝ) + 2) + 1 := by
    rw [hm]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.sqrt_nonneg _))
  have h2K : (2:ℝ) ^ (K+1) ≤ 4 * Real.sqrt ((n:ℝ) + 2) := by
    have h1 : ((2:ℕ)^K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlow
    have h2 : (2:ℝ) ^ (K+1) = 2 * ((2:ℕ)^K : ℝ) := by push_cast; ring
    calc (2:ℝ) ^ (K+1) = 2 * ((2:ℕ)^K : ℝ) := h2
      _ ≤ 2 * (m : ℝ) := by linarith
      _ ≤ 2 * (Real.sqrt ((n:ℝ) + 2) + 1) := by linarith
      _ ≤ 4 * Real.sqrt ((n:ℝ) + 2) := by nlinarith [hsq1]
  -- assemble: S1 ≤ 6B√(2^(K+1)) ≤ 6B√(4√(n+2)) = 12B√(√(n+2)) = 12B√(e^R)
  have hmain := S1mass_le_cumulative (admR n) K hRK
  have hB : (0:ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  have hsqrt_step : Real.sqrt ((2:ℝ)^(K+1))
      ≤ 2 * Real.sqrt (Real.sqrt ((n:ℝ) + 2)) := by
    calc Real.sqrt ((2:ℝ)^(K+1))
        ≤ Real.sqrt (4 * Real.sqrt ((n:ℝ) + 2)) := Real.sqrt_le_sqrt h2K
      _ = Real.sqrt 4 * Real.sqrt (Real.sqrt ((n:ℝ) + 2)) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      _ = 2 * Real.sqrt (Real.sqrt ((n:ℝ) + 2)) := by
          norm_num [show Real.sqrt 4 = 2 by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
  calc S1mass (admR n)
      ≤ 6 * (Real.log 4 + 4) * Real.sqrt ((2:ℝ)^(K+1)) := hmain
    _ ≤ 6 * (Real.log 4 + 4) * (2 * Real.sqrt (Real.sqrt ((n:ℝ) + 2))) := by
        apply mul_le_mul_of_nonneg_left hsqrt_step (by nlinarith)
    _ = 12 * (Real.log 4 + 4) * Real.sqrt (Real.sqrt ((n:ℝ) + 2)) := by ring
    _ = 12 * (Real.log 4 + 4) * Real.sqrt (Real.exp (admR n)) := by rw [hexp]

/-- Transport to the pairs-indexed defect-gate mass. -/
theorem adaptiveStageMass_le_sqrt_exp (n : ℕ) :
    adaptiveStageMass n
      ≤ 12 * (Real.log 4 + 4) * Real.sqrt (Real.exp (admR n)) := by
  rw [adaptiveStageMass_eq_S1mass]
  exact S1mass_admR_le_sqrt_exp n

#print axioms S1mass_admR_le_sqrt_exp
#print axioms adaptiveStageMass_le_sqrt_exp

end

end RHFormalization
