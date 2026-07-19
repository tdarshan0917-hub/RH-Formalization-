import RHFormalization.AdmissibleRouteHoloWired
import RHFormalization.AdmissibleGalerkinEndpoint

/-!
# AdmissibleRouteHBWired — hB DISCHARGED at the terminus

ROUTE CARD
1. Target: feed the banked `admissible_hB` into the terminus. Frontier
   drops 3 → 2: exactly h_conv (THE PILLAR) and hF remain.
2. Raw B on Ω? NO. hComb/CompensatedB targeted? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- **RH from exactly h_conv + hF at the admissible net.**
h_stage_holo and hB are discharged by banked theorems. -/
theorem RH_from_admissible_route_conv_F
    (RHcand : ℂ → ℂ)
    (h_conv :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in Filter.atTop,
            ∀ s : ℂ, s ∈ K →
              dist (galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s)
                (RHcand s) < ε)
    (hF :
      ∀ s ∈ RightHalfPlane (1 : ℝ),
        Filter.Tendsto
          (fun n : ℕ => galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s)
          Filter.atTop (nhds (FHadmFree s))) :
    RiemannHypothesis :=
  RH_from_admissible_route_conv_F_B
    RHcand
    h_conv
    hF
    (fun s hs => admissible_hB s hs)

#print axioms RH_from_admissible_route_conv_F

end

end RHFormalization
