import RHFormalization.DesignedRCutoffS
import RHFormalization.AppendixDRCutoffEstimateDetailedConstruction

/-!
# RHFormalization.DesignedDetailedConstruction

The first complete D-side witness: `designedY : DDetailedConstructionWithOperatorLegality`,
assembled from the designed operator layer, the prime-power stage ladder, and the
R-cutoff estimate instance. All limits ride the proven exhaustion machinery; all
residual obligations vanish by the R ≡ 0 design; all s-uniformity collapses by the
s-independence of the displacement kernel.
-/

namespace RHFormalization

noncomputable section

open Complex

/-- Notation anchors. -/
private abbrev dP : DFiniteStagePackage := designedFiniteOperatorLayer.toStagePackage
private abbrev dC : CanonicalPrimePowerPackage :=
  RCutoffEstimateSharedPackage designedFiniteOperatorLayer designedRCutoffS

/-- The evaluation point 2 lies in the designed overlap half-plane. -/
theorem two_mem_designed_halfplane : (2 : ℂ) ∈ RightHalfPlane dP.sigma0 := by
  show dP.sigma0 < (2 : ℂ).re
  rw [designedFiniteOperatorLayer_sigma0]
  norm_num

/-- Constants are holomorphic. -/
theorem holomorphicOnC_const (c : ℂ) (U : Set ℂ) :
    HolomorphicOnC (fun _ : ℂ => c) U := by
  first
    | exact analyticOn_const
    | exact analyticOnNhd_const
    | intro x hx; exact analyticWithinAt_const

/-- The designed shared B-function is constant in s. -/
theorem designed_Bshared_const :
    dC.Bshared = fun _ : ℂ => dC.Bshared 2 := rfl

/-- The pointwise stage limit at s = 2, in B_stage form. -/
theorem designed_B_stage_tendsto :
    Filter.Tendsto (fun n : ℕ => dP.B_stage (primePowerStage n) 2)
      Filter.atTop (nhds (dC.Bshared 2)) := by
  have hL :=
    (RCutoffEstimateFiniteCanonicalLimit designedFiniteOperatorLayer
      designedRCutoffS).h_finiteCanonical_tendsto_Bshared 2 two_mem_designed_halfplane
  refine Filter.Tendsto.congr (fun n => ?_) hL
  exact
    (designedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula.h_B_stage_eq_finiteCanonical
      (primePowerStage n) 2).symm

/-- The designed window: stage kernel already equals the limit kernel. -/
noncomputable def designedW : DCanonicalWindowData :=
  { gbar_stage := fun _ a => heatKernelG 1 a
    G_limit := heatKernelG 1
    c_w := 1 }

noncomputable def designedWapi : DCanonicalWindowAPI designedW :=
  { alpha := primePowerStage
    h_cw_eq_one := rfl
    h_local_uniform_window := by
      intro A _ ε hε
      filter_upwards with n a _
      show dist (heatKernelG 1 a) ((1 : ℂ) * heatKernelG 1 a) < ε
      simpa [one_mul, dist_self] using hε }

/-- The designed FH-limit: FH is the shared B-function itself. -/
noncomputable def designedF : DFHLimitData dP :=
  { alpha := primePowerStage
    FH := dC.Bshared
    h_FH_holo := by
      rw [designed_Bshared_const]
      exact holomorphicOnC_const _ _
    h_F_stage_to_FH := by
      intro K _ _ ε hε
      have hev := (Metric.tendsto_nhds.mp designed_B_stage_tendsto) ε hε
      filter_upwards [hev] with n hn s _
      first
        | exact hn
        | simpa using hn }

noncomputable def designedSectors : DResidualSectorData dP :=
  { sectorPart := fun _ _ _ => 0 }

noncomputable def designedSplit : DResidualSectorSplitAPI dP designedSectors :=
  { h_recombine := by
      intro α s
      rw [show dP.R_stage α s = 0 from designedFiniteOperatorLayer_R_stage_eq_zero α s]
      show (0 : ℂ) = 0 + 0 + 0 + 0
      norm_num }

noncomputable def designedBounds : DResidualSectorBoundsAPI dP designedSectors :=
  { h_sector_bound := by
      intro sector K _ _
      refine ⟨0, le_refl 0, ?_⟩
      intro α s _
      show ‖(0 : ℂ)‖ ≤ 0
      simp }

noncomputable def designedMaster : DMasterResidualAPI dP designedSectors :=
  { h_master := fun _ _ =>
      { alpha := primePowerStage
        RH := fun _ => 0
        h_RH_holo := holomorphicOnC_const 0 Ω
        h_R_stage_to_RH := by
          intro K _ _ ε hε
          filter_upwards with n s _
          rw [show dP.R_stage (primePowerStage n) s = 0 from
            designedFiniteOperatorLayer_R_stage_eq_zero (primePowerStage n) s]
          simpa [dist_self] using hε } }

/-- THE FIRST COMPLETE D-SIDE WITNESS. -/
noncomputable def designedY : DDetailedConstructionWithOperatorLegality :=
  buildDDetailedConstructionWithOperatorLegalityFromRCutoffEstimate
    designedFiniteOperatorLayer
    designedRCutoffS
    designedW
    designedWapi
    designedF
    designedSectors
    designedSplit
    designedBounds
    designedMaster
    { h_overlap := by
        intro s hs
        have hm :=
          (buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
            designedFiniteOperatorLayer
            dC
            (RCutoffEstimateFiniteCanonicalLimit designedFiniteOperatorLayer
              designedRCutoffS)).h_Bcan_matches_shared s hs
        show dC.Bshared s = _ + (0 : ℂ)
        rw [hm, add_zero]
        first
          | rfl
          | simp [buildDBcanLimitDataFromOperatorFiniteCanonicalLimit,
              buildDBcanLimitDataFromOperatorPrimePowerLimit] }

/-- The designed Y's B-function is the genuine prime-power tsum. -/
theorem designedY_Bcan_eq_tsum
    (s : ℂ) (hs : s ∈ RightHalfPlane dP.sigma0) :
    designedY.B.Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * (displacementCanonicalKernel (heatKernelG 1)) q.center s := by
  exact
    detailedConstructionFromRCutoffEstimate_Bcan_matches_tsum
      designedFiniteOperatorLayer designedRCutoffS designedW designedWapi designedF
      designedSectors designedSplit designedBounds designedMaster _ s hs

#print axioms designedY
#print axioms designedY_Bcan_eq_tsum

end

end RHFormalization
