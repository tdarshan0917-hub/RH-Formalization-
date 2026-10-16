import RHFormalization.PolylogCenteredAbel
import Mathlib

/-!
# PolylogMainTermIncrement — PL-4b-ii-1: main-term increments

`mainIncr z k = ((k+1)^z − k^z)/z`.  The increments telescope to `(M^z − 0^z)/z`,
and for `k ≥ 1`, `ρ ≠ 1`, the increment at `z = 1 − ρ` is `∫_k^{k+1} x^{−ρ} dx`.
This writes the main term `M^{1−ρ}/(1−ρ)` as a sum whose shift by `k^{−δ}` can be
compared term by term (PL-4b-ii-2).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- Main-term increment `((k+1)^z − k^z)/z`. -/
def mainIncr (z : ℂ) (k : ℕ) : ℂ := (((k:ℂ) + 1) ^ z - (k:ℂ) ^ z) / z

/-- The increments telescope. -/
theorem sum_mainIncr (z : ℂ) (M : ℕ) :
    ∑ k ∈ Finset.range M, mainIncr z k = (((M:ℂ)) ^ z - (0:ℂ) ^ z) / z := by
  induction M with
  | zero => simp [mainIncr]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    unfold mainIncr
    push_cast
    ring

/-- Integral representation of an increment away from the origin. -/
theorem mainIncr_eq_integral {ρ : ℂ} (hρ : ρ ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    mainIncr (1 - ρ) k = ∫ x in (k:ℝ)..((k:ℝ) + 1), (x:ℂ) ^ (-ρ) := by
  have hcond : -1 < (-ρ).re ∨ (-ρ ≠ -1 ∧ (0:ℝ) ∉ Set.uIcc (k:ℝ) ((k:ℝ) + 1)) := by
    right
    refine ⟨fun h => hρ (by linear_combination -h), ?_⟩
    rw [Set.uIcc_of_le (by linarith)]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  rw [integral_cpow hcond, show -ρ + 1 = 1 - ρ by ring]
  unfold mainIncr
  push_cast
  first | rfl | ring

#print axioms sum_mainIncr
#print axioms mainIncr_eq_integral

end

end RHFormalization
