import RHFormalization.DecodedRouteTerminus
import RHFormalization.AdmissibleRStageHolo

/-!
# AdmissibleRouteHoloWired — h_stage_holo CONSUMED at the terminus

ROUTE CARD
1. Target: instantiate the live terminus at the admissible net and
   discharge input (1) h_stage_holo with the banked
   `admissible_R_stage_holo`. The elaborator certifies the package
   alignment the terminus route card flagged as pending.
2. Frontier reduction: obligations drop 4 → 3 (h_conv, hF, hB).
   h_conv remains THE PILLAR. No new hypotheses introduced.
3. Raw B on Ω? NO. hComb/CompensatedB/Combined targeted? NO (routing
   verdict 2026-07-19 honored).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- **The terminus at the admissible net with h_stage_holo DISCHARGED.**
Remaining live obligations: h_conv (the pillar), hF, hB. -/
theorem RH_from_admissible_route_conv_F_B
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
          Filter.atTop (nhds (FHadmFree s)))
    (hB :
      ∀ s ∈ RightHalfPlane (1 : ℝ),
        Filter.Tendsto
          (fun n : ℕ => galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
          Filter.atTop (nhds (galerkinBcanLimitData.Bcan s))) :
    RiemannHypothesis :=
  RH_from_decoded_route_inputs
    admissibleGalerkinStageSeq
    RHcand
    (fun n => admissible_R_stage_holo n)
    h_conv
    hF
    hB

#print axioms RH_from_admissible_route_conv_F_B

end

end RHFormalization
