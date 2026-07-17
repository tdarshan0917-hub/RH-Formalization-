import RHFormalization.ShiftedLaplaceFiniteOperatorLayer
import RHFormalization.DOperatorExport

namespace RHFormalization

noncomputable section

/-- The shifted-Laplace Appendix-D operator export: the canonical transform `FH_can`,
its Ω-holomorphy, and compact-local convergence of the finite stages. This is exactly
the data of `DFHLimitData` for the shifted operator layer. -/
def shiftedLaplaceDFHExport
    (FH_can : ℂ → ℂ)
    (alpha : ℕ → DFiniteStage)
    (h_FH_holo : HolomorphicOnC FH_can Ω)
    (h_F_stage_to_FH :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in Filter.atTop,
            ∀ s : ℂ, s ∈ K →
              dist (shiftedLaplaceFiniteOperatorLayer.toStagePackage.F_stage (alpha n) s)
                (FH_can s) < ε) :
    DFHLimitData shiftedLaplaceFiniteOperatorLayer.toStagePackage :=
  { alpha := alpha
    FH := FH_can
    h_FH_holo := h_FH_holo
    h_F_stage_to_FH := h_F_stage_to_FH }

end

end RHFormalization
