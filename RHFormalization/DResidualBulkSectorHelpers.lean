import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthAlignedDetailedConstruction
import RHFormalization.DResidualSectorBoundsConcrete
import RHFormalization.DMasterResidualConcrete

/-!
# RHFormalization.DResidualBulkSectorHelpers

Generic helpers that package the finite-stage residual `P.R_stage` as one
bulk sector. This removes residual-sector bookkeeping from selected Appendix-D
routes.

The only genuine extra input is a compact-uniform bound for `P.R_stage` on
Ω-compacts.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Put the entire residual stage function into the `bulk` sector, and set the
other residual sectors to zero.
-/
def residualBulkSectorData (P : DFiniteStagePackage) :
    DResidualSectorData P :=
  { sectorPart := fun sector α s =>
      match sector with
      | DResidualSector.short => 0
      | DResidualSector.window => 0
      | DResidualSector.tail => 0
      | DResidualSector.bulk => P.R_stage α s }

/--
The bulk-sector data recombines to the full finite-stage residual.
-/
theorem residualBulkSectorSplitAPI
    (P : DFiniteStagePackage) :
    DResidualSectorSplitAPI P (residualBulkSectorData P) := by
  refine ⟨?_⟩
  intro α s
  simp [residualBulkSectorData, add_assoc]

/--
If `P.R_stage` is uniformly bounded on Ω-compacts, then the bulk-sector package
satisfies the residual-sector bounds API.
-/
theorem residualBulkSectorBoundsAPI_of_R_stage_bound
    (P : DFiniteStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ),
        IsCompact K →
        K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖P.R_stage α s‖ ≤ C) :
    DResidualSectorBoundsAPI P (residualBulkSectorData P) := by
  refine ⟨?_⟩
  intro sector K hK hKOmega
  cases sector
  · refine ⟨0, le_rfl, ?_⟩
    intro α s hs
    simp [residualBulkSectorData]
  · refine ⟨0, le_rfl, ?_⟩
    intro α s hs
    simp [residualBulkSectorData]
  · refine ⟨0, le_rfl, ?_⟩
    intro α s hs
    simp [residualBulkSectorData]
  · exact h_R_stage_bound K hK hKOmega

/--
A master residual API that ignores the sector proof arguments and returns the
given residual limit data.
-/
def masterResidualAPI_from_data
    {P : DFiniteStagePackage}
    (R : DMasterResidualData P) :
    DMasterResidualAPI P (residualBulkSectorData P) :=
  { h_master := fun _ _ => R }

end

end RHFormalization
