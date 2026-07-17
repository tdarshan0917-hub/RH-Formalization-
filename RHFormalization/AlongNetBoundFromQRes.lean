import RHFormalization.ResidualLaplaceRep
import RHFormalization.PrimePerturbedDCANREMNetTarget
import RHFormalization.GalerkinDuhamelUniformBound
import RHFormalization.AnchorFinite
import Mathlib

/-!
# Along-net R_stage bound from the time-side residual integral (D.USR assembly).

R_stage = F − B = ∫ e^{-st} Q_res (Stieltjes identity, green mod connector).
‖R_stage‖ ≤ ∫|Q_res| ≤ (cutoff-independent Galerkin/Duhamel bound) = densityAnchor·compactFactor.

This packages the along-net bound as a reduction to ONE sector hypothesis
(the cutoff-independent ∫|Q_res| ≤ C bound), then converts to h_loc_bdd via the
banked bridge. The sector hypothesis is supplied by the banked Galerkin uniform bound.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- The along-net R_stage bound holds if the time-side residual integral is uniformly
bounded on each compact (the cutoff-independent sector bound). This is the D.USR core:
‖∫ e^{-st} Q_res‖ ≤ C uniform in the cutoff n. -/
theorem primePerturbedAligned_along_bound_from_qRes_bound
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (hQ : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C) :
    PrimePerturbedAlignedAlongRStageBound μ alpha := by
  intro K hK hKΩ
  exact hQ K hK hKΩ

/-- **D.USR ⇒ h_loc_bdd** for the aligned prime layer: the uniform residual bound
gives Montel's local-boundedness input. -/
theorem primePerturbedAligned_h_loc_bdd_from_qRes_bound
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (hQ : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C :=
  primePerturbedAligned_h_loc_bdd_from_along_bound μ alpha
    (primePerturbedAligned_along_bound_from_qRes_bound μ alpha hQ)

#print axioms primePerturbedAligned_h_loc_bdd_from_qRes_bound

end RHFormalization
