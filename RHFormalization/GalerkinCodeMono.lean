/-
GalerkinCodeMono.lean

CODE-SET MONOTONICITY along the exhaustion: the active prime-power pair
sets and their Nat code images are monotone in the cutoff R. Structural
input for the code-drift (D.R->infty) half of the N-limit.
-/
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff

namespace RHFormalization

/-- The active pair set is monotone in the cutoff. -/
theorem activePrimePowerPairsCenterBelow_mono {R R' : ℝ} (h : R ≤ R') :
    activePrimePowerPairsCenterBelow R ⊆ activePrimePowerPairsCenterBelow R' := by
  intro q hq
  rw [activePrimePowerPairsCenterBelow_mem] at hq ⊢
  exact ⟨hq.1, le_trans hq.2 h⟩

/-- The active code set is monotone in the cutoff. -/
theorem activePrimePowerCodesCenterBelow_mono {R R' : ℝ} (h : R ≤ R') :
    activePrimePowerCodesCenterBelow R ⊆ activePrimePowerCodesCenterBelow R' := by
  unfold activePrimePowerCodesCenterBelow
  exact Finset.image_subset_image (activePrimePowerPairsCenterBelow_mono h)

#print axioms activePrimePowerPairsCenterBelow_mono
#print axioms activePrimePowerCodesCenterBelow_mono

end RHFormalization
