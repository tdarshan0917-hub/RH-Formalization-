-- SENTINEL: R0-v1
import RHFormalization.AdmissibleFirstOrderVanish

/-!
# S₁ mass at the admissible cutoff: sqrt-rate bound (defect-gate R0)

`admR n = log(n+2)/2` gives `exp (admR n) = √(n+2)`, so the banked
`S1mass_le : S1mass R ≤ 2·(e^R + 2)` sharpens along the schedule to
`S1mass (admR n) ≤ 2·(√(n+2) + 2)`.

This is the rate that closes the defect-gate weighted stage sum
(G4 step 2): stage mass × O(1/(n+2)) per-spike tail → 0 like (n+2)^{-1/2}.
The banked linear bound `S1mass_admR_le_linear ≤ 6(n+2)` is lossy
(it slackened the /2 in admR); this brick recovers the true rate.
-/

namespace RHFormalization

/-- `exp (admR n) = √(n+2)`, the exact evaluation of the schedule cutoff. -/
theorem exp_admR_eq_sqrt (n : ℕ) :
    Real.exp (admR n) = Real.sqrt ((n : ℝ) + 2) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hadm : admR n = Real.log ((n : ℝ) + 2) / 2 := by
    first
      | rfl
      | unfold admR
      | simp only [admR]
  have hsq : (Real.exp (Real.log ((n : ℝ) + 2) / 2)) ^ 2 = (n : ℝ) + 2 := by
    rw [sq, ← Real.exp_add, add_halves]
    exact Real.exp_log hpos
  calc Real.exp (admR n)
      = Real.exp (Real.log ((n : ℝ) + 2) / 2) := by rw [hadm]
    _ = Real.sqrt ((Real.exp (Real.log ((n : ℝ) + 2) / 2)) ^ 2) := by
        rw [Real.sqrt_sq (Real.exp_pos _).le]
    _ = Real.sqrt ((n : ℝ) + 2) := by rw [hsq]

/-- **Sqrt-rate S₁ bound along the admissible schedule**:
`S₁(admR n) ≤ 2·(√(n+2) + 2)`. -/
theorem S1mass_admR_le_sqrt (n : ℕ) :
    S1mass (admR n) ≤ 2 * (Real.sqrt ((n : ℝ) + 2) + 2) := by
  have h1 := S1mass_le (admR n)
  rw [exp_admR_eq_sqrt] at h1
  exact h1

#print axioms exp_admR_eq_sqrt
#print axioms S1mass_admR_le_sqrt

end RHFormalization
