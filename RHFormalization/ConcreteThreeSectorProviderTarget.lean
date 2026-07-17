import RHFormalization.PrimeDUSRAssembly
import RHFormalization.DLocSectorBound
import RHFormalization.DDispSectorBound
import RHFormalization.DTailUniformBound
import Mathlib

/-!
# Concrete three-sector provider target for the honest Appendix-D route.

This records the exact remaining D.USR provider:
construct Qloc, Qdisp, Rtail, anchor, factor for the aligned prime layer, prove
R_stage = Qloc + Qdisp + Rtail, and feed the clean three-sector assembly.

No proof is attempted here yet. This file is the permanent target file.
-/

namespace RHFormalization
open Complex
open scoped BigOperators

def ConcreteThreeSectorProviderTarget {N : ℕ}
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage) : Prop :=
  ∃ (Qloc Qdisp Rtail : DFiniteStage → ℂ → ℂ)
    (anchor : ℕ → ℝ) (factor : Set ℂ → ℝ),
    (∀ n, 0 ≤ anchor n) ∧
    (∃ A : ℝ, 0 ≤ A ∧ ∀ n, anchor n ≤ A) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → 0 ≤ factor K) ∧
    (∀ n s,
      (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s =
        Qloc (alpha n) s + Qdisp (alpha n) s + Rtail (alpha n) s) ∧
    (∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K,
      ‖Qloc (alpha n) s‖ ≤ anchor n * factor K) ∧
    (∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K,
      ‖Qdisp (alpha n) s‖ ≤ anchor n * factor K) ∧
    (∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K,
      ‖Rtail (alpha n) s‖ ≤ anchor n * factor K)

/-- The concrete provider closes Montel local boundedness for the aligned prime layer. -/
theorem primePerturbedAligned_h_loc_bdd_from_concrete_three_sector_provider
    {N : ℕ} (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (H : ConcreteThreeSectorProviderTarget μ alpha) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C := by
  rcases H with ⟨Qloc, Qdisp, Rtail, anchor, factor,
    h_anchor_nonneg, h_anchor_bound, h_factor_nonneg,
    h_decomp, h_loc_le, h_disp_le, h_tail_le⟩
  exact primePerturbedAligned_h_loc_bdd_from_three_sectors
    μ alpha Qloc Qdisp Rtail anchor factor
    h_anchor_nonneg h_anchor_bound h_factor_nonneg
    h_decomp h_loc_le h_disp_le h_tail_le

#print axioms ConcreteThreeSectorProviderTarget
#print axioms primePerturbedAligned_h_loc_bdd_from_concrete_three_sector_provider

end RHFormalization
