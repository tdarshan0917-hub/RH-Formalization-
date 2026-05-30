import RHFormalization.DOperatorExport

/-!
# RHFormalization.DResidualSectorBoundsConcrete

Theorem-backed helper layer for D residual sector compact bounds.

This file is not an RH endpoint.

It records the concrete compact-uniform estimate now required by
`DResidualSectorBoundsAPI`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Build residual sector bounds from explicit compact-uniform estimates.
-/
def buildDResidualSectorBoundsAPIFromCompactUniform
    (P : DFiniteStagePackage)
    (S : DResidualSectorData P)
    (h_sector_bound :
      ∀ sector : DResidualSector,
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∃ C : ℝ,
            0 ≤ C ∧
              ∀ α : DFiniteStage,
              ∀ s : ℂ,
                s ∈ K →
                  ‖S.sectorPart sector α s‖ ≤ C) :
    DResidualSectorBoundsAPI P S :=
  { h_sector_bound := h_sector_bound }

/--
Accessor theorem: each sector has a compact-uniform bound on every compact
`K ⊆ Ω`.
-/
theorem DResidualSectorBoundsAPI.exists_compact_uniform_bound
    {P : DFiniteStagePackage}
    {S : DResidualSectorData P}
    (B : DResidualSectorBoundsAPI P S)
    (sector : DResidualSector)
    (K : Set ℂ)
    (hK : IsCompact K)
    (hKOmega : K ⊆ Ω) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ α : DFiniteStage,
        ∀ s : ℂ,
          s ∈ K →
            ‖S.sectorPart sector α s‖ ≤ C :=
  B.h_sector_bound sector K hK hKOmega

end

end RHFormalization
