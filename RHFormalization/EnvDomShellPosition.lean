import Mathlib
set_option autoImplicit false
open Real

namespace RHFormalization

/-- **A.ENV-DOM, shell position inequality.** For `q` in logarithmic shell `k`
(`k ≤ log q < k+1`), the displacement from `u` to the prime center `log q` is
controlled by the displacement to the integer shell index `k`:
`|u − log q| ≥ |u − k| − 1` (manuscript A.ENV-DOM p.54). -/
theorem shell_position_bound
    (k : ℕ) (u : ℝ) (lq : ℝ)
    (hlo : (k : ℝ) ≤ lq) (hhi : lq < (k : ℝ) + 1) :
    |u - lq| ≥ |u - (k : ℝ)| - 1 := by
  -- |log q − k| < 1  (since 0 ≤ log q − k < 1)
  have hclose : |lq - (k : ℝ)| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  -- triangle: |u − k| ≤ |u − log q| + |log q − k|
  have htri : |u - (k : ℝ)| ≤ |u - lq| + |lq - (k : ℝ)| := by
    calc |u - (k : ℝ)| = |(u - lq) + (lq - (k : ℝ))| := by ring_nf
      _ ≤ |u - lq| + |lq - (k : ℝ)| := abs_add_le _ _
  linarith [htri, hclose]

#print axioms shell_position_bound

end RHFormalization
