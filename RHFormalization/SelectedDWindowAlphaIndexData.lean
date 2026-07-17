import RHFormalization.CanonicalPrimePowerSharpCutoffClosedDWindowSourceFromFactorBounds
import RHFormalization.SelectedFiniteOperatorLayer

/-!
# Selected D-window alpha/index source

This is the small source package needed by
`selectedDWindowSoundCountingFactorBoundsData`.

It is not a new route. It isolates exactly the next four fields:
`alpha`, `h_R_ge_nat`, index containment, and index subset.
-/

namespace RHFormalization

noncomputable section

structure SelectedDWindowAlphaIndexData where
  alpha : ℕ → DFiniteStage

  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

  h_indices_contains_of_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      IsPrimePowerPair q →
      q.center ≤ (alpha n).R →
        q ∈ selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  h_indices_subset_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        q.center ≤ (alpha n).R

end

end RHFormalization
