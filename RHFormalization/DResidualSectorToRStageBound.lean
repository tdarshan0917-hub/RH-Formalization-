import RHFormalization.DOperatorExport

/-!
# Sector bounds ⇒ `R_stage` compact bound

Plank 3: the first plank whose conclusion is literally the shape of `h_R_stage_bound`.
`R_stage` recombines as `short + window + tail + bulk`; if each sector is uniformly bounded
on every compact `K ⊆ Ω` independently of the stage, so is `R_stage` (4-way triangle + sum).
Reduces the assumed `h_R_stage_bound` to the four granular sector bounds (the D.DISP/D.ADM
estimates; short = displacement sector where `gaussian_penalty_le_pow` feeds).
-/

namespace RHFormalization
noncomputable section
open Complex

/-- **Sector bounds ⇒ `R_stage` compact bound (Plank 3).** -/
theorem R_stage_bound_of_sector_bounds
    (P : DFiniteStagePackage) (S : DResidualSectorData P)
    (split : DResidualSectorSplitAPI P S) (bounds : DResidualSectorBoundsAPI P S) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ α : DFiniteStage, ∀ s ∈ K, ‖P.R_stage α s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨Cs, hCs0, hCs⟩ := bounds.h_sector_bound DResidualSector.short K hK hKΩ
  obtain ⟨Cw, hCw0, hCw⟩ := bounds.h_sector_bound DResidualSector.window K hK hKΩ
  obtain ⟨Ct, hCt0, hCt⟩ := bounds.h_sector_bound DResidualSector.tail K hK hKΩ
  obtain ⟨Cb, hCb0, hCb⟩ := bounds.h_sector_bound DResidualSector.bulk K hK hKΩ
  refine ⟨Cs + Cw + Ct + Cb, by positivity, ?_⟩
  intro α s hs
  rw [split.h_recombine α s]
  have ht : ‖S.sectorPart DResidualSector.short α s
        + S.sectorPart DResidualSector.window α s
        + S.sectorPart DResidualSector.tail α s
        + S.sectorPart DResidualSector.bulk α s‖
      ≤ ‖S.sectorPart DResidualSector.short α s‖
        + ‖S.sectorPart DResidualSector.window α s‖
        + ‖S.sectorPart DResidualSector.tail α s‖
        + ‖S.sectorPart DResidualSector.bulk α s‖ := by
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    exact norm_add_le _ _
  refine le_trans ht ?_
  gcongr
  · exact hCs α s hs
  · exact hCw α s hs
  · exact hCt α s hs
  · exact hCb α s hs

#print axioms R_stage_bound_of_sector_bounds
end
end RHFormalization
