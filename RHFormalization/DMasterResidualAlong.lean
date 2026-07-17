import RHFormalization.DOperatorExport
import RHFormalization.DMasterResidualConcrete
import RHFormalization.FHHoloFromStages

/-!
# `DMasterResidualData` along the admissible cutoff net

The D.CAN-REM object the bridge consumes: holomorphic limit `RH ∈ O(Ω)` + local-uniform
convergence `R_stage (alpha n) → RH`. Stated ALONG the admissible net `alpha : ℕ → DFiniteStage`,
not over arbitrary `DFiniteStage`. Holomorphy of the limit is derived via the Weierstrass engine
`FH_holo_from_stage_epsN`, not assumed. Isolates the two genuine along-alpha inputs:
stage holomorphy (finite F−B, elementary) and the density-normalized convergence (the crux).
-/

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- **D.MASTER-RESIDUAL along the admissible net.** -/
def buildDMasterResidualDataAlong
    (P : DFiniteStagePackage)
    (alpha : ℕ → DFiniteStage)
    (RH : ℂ → ℂ)
    (h_stage_holo : ∀ n : ℕ, HolomorphicOnC (fun s => P.R_stage (alpha n) s) Ω)
    (h_conv :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∀ ε : ℝ,
            0 < ε →
              ∀ᶠ n in Filter.atTop,
                ∀ s : ℂ,
                  s ∈ K →
                    dist (P.R_stage (alpha n) s) (RH s) < ε) :
    DMasterResidualData P :=
  buildDMasterResidualDataFromCompactUniform P alpha RH
    (FH_holo_from_stage_epsN
      (fun n s => P.R_stage (alpha n) s) RH h_stage_holo h_conv)
    h_conv

#print axioms buildDMasterResidualDataAlong

end
end RHFormalization
