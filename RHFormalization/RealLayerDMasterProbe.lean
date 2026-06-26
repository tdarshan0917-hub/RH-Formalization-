import RHFormalization.DCanRemFromMontel
import RHFormalization.MontelSubsequenceAssembly
import RHFormalization.AscoliBridgeLayer3
import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.EquicontinuousFromLocBdd
import Mathlib

set_option autoImplicit false

/-!
# Real-layer DMaster (Montel route, F-B kernel) — hRC DISCHARGED (Milestone C).

hRC is no longer a hypothesis. It is supplied internally from the green brick
ascoliExtractionHyp_of_holo_loc_bdd, fed the same h_loc_bdd already required.
Remaining inputs: h_stage_holo, h_loc_bdd, h_overlap, hRH_holo — all green-sourced.
-/

namespace RHFormalization
noncomputable section
open Filter Topology

variable {N : ℕ}

/-- Real-layer DMaster via the proven Montel route, hRC discharged internally. -/
def realLayerDMaster
    (μ : Fin N → ℝ)
    (alpha : ℕ → DFiniteStage)
    (R_H : ℂ → ℂ)
    (h_stage_holo : ∀ n : ℕ,
        HolomorphicOnC
          (fun s => (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s) Ω)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K,
          ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C)
    (h_overlap : ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
        ∀ s ∈ U, Tendsto
          (fun n => (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s)
          atTop (nhds (R_H s)))
    (hRH_holo : HolomorphicOnC R_H Ω) :
    DMasterResidualData (primePerturbedOperatorLayerAligned μ).toStagePackage :=
  -- hRC supplied internally from the green brick, fed the same h_loc_bdd
  have hRC : AscoliExtractionHyp
      (fun n s => (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s) :=
    ascoliExtractionHyp_of_holo_loc_bdd
      (fun n s => (primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s)
      h_loc_bdd
  dcanrem_from_montel
    (primePerturbedOperatorLayerAligned μ).toStagePackage
    alpha
    R_H
    h_stage_holo
    h_loc_bdd
    h_overlap
    (holomorphicMontelConvergence_from_ascoli hRH_holo
      (ascoliExtraction_of_relativelyCompact hRC))

#print axioms realLayerDMaster

end
end RHFormalization
