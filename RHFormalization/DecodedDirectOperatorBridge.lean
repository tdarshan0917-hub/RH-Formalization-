-- SENTINEL: decoded-direct-operator-bridge-v1
import RHFormalization.AnnexSpine
import RHFormalization.AdmissibleBConvReduction
import RHFormalization.AdmissibleGalerkinEndpoint
import RHFormalization.GalerkinStagePackage
import RHFormalization.DOverlapPointwiseFromCompactUniform
import RHFormalization.HalfPlaneGeometry
import Mathlib

/-!
# Direct OperatorResolventBridge — the DFHLimitData bypass
UPSTREAM: OperatorResolventBridge is FLAT (AnnexSpine.lean:32): FH,B,RH,sigma0,
  two holos, h_split on RightHalfPlane sigma0 ONLY. FHadmFree_holo banked.
  DMasterResidualData supplies RH + holo + compact-uniform R (→ pointwise on
  overlap via singletons). Stage split definitional (galerkinStageSplitAPI).
TARGET: OperatorResolventBridge from (R, hF-overlap-pointwise, hB-overlap-pointwise).
DOWNSTREAM CONSUMER: RH_from_D_E (HonestEndpointV6.lean:23) — terminus takes
  any D : OperatorResolventBridge + E : InterfaceBridgeNonnegativeAPI D.
SEMANTIC: BYPASSES the jointly-uninhabitable (DFHLimitData, DMasterResidualData)
  pair (roadmap 2026-07-16 OBSTRUCTION FINDING). No compact-uniform F demand.
  h_split = Y2 uniqueness pattern on the overlap. sigma0 = 1 (package value).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- **The DFHLimitData bypass**: build the flat bridge the E/F spine consumes
directly from the master-residual data plus overlap-pointwise F/B limits. -/
def decodedDirectOperatorBridge
    (R : DMasterResidualData galerkinStagePackage)
    (hF :
      ∀ s ∈ RightHalfPlane (1 : ℝ),
        Filter.Tendsto
          (fun n : ℕ => galerkinStagePackage.F_stage (R.alpha n) s)
          Filter.atTop (nhds (FHadmFree s)))
    (hB :
      ∀ s ∈ RightHalfPlane (1 : ℝ),
        Filter.Tendsto
          (fun n : ℕ => galerkinStagePackage.B_stage (R.alpha n) s)
          Filter.atTop (nhds (galerkinBcanLimitData.Bcan s))) :
    OperatorResolventBridge :=
  { FH := FHadmFree
    B := galerkinBcanLimitData.Bcan
    RH := R.RH
    sigma0 := 1
    hFH_holo := FHadmFree_holo
    hRH_holo := R.h_RH_holo
    h_split := by
      intro s hs
      have hRHP : RightHalfPlane galerkinStagePackage.sigma0 ⊆ Ω := by
        first
          | exact rightHalfPlane_subset_Omega galerkinStagePackage.sigma0
              (by norm_num [galerkinStagePackage])
          | exact rightHalfPlane_subset_Omega 1 (by norm_num)
      have hs' : s ∈ RightHalfPlane galerkinStagePackage.sigma0 := by
        first
          | exact hs
          | simpa [galerkinStagePackage] using hs
      have hRlim :
          Filter.Tendsto
            (fun n : ℕ => galerkinStagePackage.R_stage (R.alpha n) s)
            Filter.atTop (nhds (R.RH s)) :=
        R.pointwise_R_stage_tendsto_of_RHP_subset_Omega hRHP s hs'
      have hBRlim :
          Filter.Tendsto
            (fun n : ℕ =>
              galerkinStagePackage.B_stage (R.alpha n) s
                + galerkinStagePackage.R_stage (R.alpha n) s)
            Filter.atTop
            (nhds (galerkinBcanLimitData.Bcan s + R.RH s)) :=
        (hB s hs).add hRlim
      have hFeqBR :
          (fun n : ℕ => galerkinStagePackage.F_stage (R.alpha n) s)
            = (fun n : ℕ =>
                galerkinStagePackage.B_stage (R.alpha n) s
                  + galerkinStagePackage.R_stage (R.alpha n) s) := by
        funext n
        exact galerkinStageSplitAPI.h_stage_split (R.alpha n) s hs'
      have hBR_to_FH :
          Filter.Tendsto
            (fun n : ℕ =>
              galerkinStagePackage.B_stage (R.alpha n) s
                + galerkinStagePackage.R_stage (R.alpha n) s)
            Filter.atTop (nhds (FHadmFree s)) := by
        simpa [hFeqBR] using hF s hs
      exact tendsto_nhds_unique hBR_to_FH hBRlim }

#print axioms decodedDirectOperatorBridge

end

end RHFormalization
