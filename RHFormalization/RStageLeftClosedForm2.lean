import RHFormalization.RStageLeftClosedForm

namespace RHFormalization
noncomputable section
open Complex Filter Topology

/-- Each summand of the Mittag-Leffler cotangent series, in resolvent form.
For `x ∈ ℂ_ℤ` and `n : ℕ+`, the paired term equals `2x/(x²-n²)`. -/
theorem cot_series_summand_resolvent (x : ℂ) (hx : x ∈ Complex.integerComplement) (n : ℕ+) :
    1/(x - (n:ℂ)) + 1/(x + (n:ℂ)) = (2*x)/(x^2 - (n:ℂ)^2) := by
  have hpos : (0:ℂ) < (n:ℝ) := by exact_mod_cast n.pos
  have hne : ((n:ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr n.ne_zero)
  -- x is not an integer, so x ≠ ±n
  have h1 : x - (n:ℂ) ≠ 0 := by
    intro h
    apply hx
    refine ⟨(n:ℤ), ?_⟩
    have : x = (n:ℂ) := by linear_combination h
    rw [this]; push_cast; ring
  have h2 : x + (n:ℂ) ≠ 0 := by
    intro h
    apply hx
    refine ⟨-(n:ℤ), ?_⟩
    have : x = -(n:ℂ) := by linear_combination h
    rw [this]; push_cast; ring
  have hfac : x^2 - (n:ℂ)^2 = (x - (n:ℂ)) * (x + (n:ℂ)) := by ring
  rw [hfac, div_add_div _ _ h1 h2]
  congr 1
  ring

#print axioms cot_series_summand_resolvent
end
end RHFormalization
