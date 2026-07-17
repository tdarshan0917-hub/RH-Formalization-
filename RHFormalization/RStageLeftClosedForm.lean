import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

namespace RHFormalization
noncomputable section
open Complex Filter Topology

/-- The paired cotangent term equals the single rational `2x/(x²-(n+1)²)`. -/
theorem cotTerm_pair_eq (x : ℂ) (n : ℕ)
    (h1 : x - ((n:ℂ)+1) ≠ 0) (h2 : x + ((n:ℂ)+1) ≠ 0) :
    1/(x-((n:ℂ)+1)) + 1/(x+((n:ℂ)+1)) = (2*x)/(x^2 - ((n:ℂ)+1)^2) := by
  have hfac : x^2 - ((n:ℂ)+1)^2 = (x-((n:ℂ)+1)) * (x+((n:ℂ)+1)) := by ring
  rw [hfac, div_add_div _ _ h1 h2]
  congr 1
  ring

#print axioms cotTerm_pair_eq
end
end RHFormalization
