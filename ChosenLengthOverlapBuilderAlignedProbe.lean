import RHFormalization.DOverlapPointwiseFromCompactUniform
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthDetailedConstruction
import RHFormalization.AppendixDPrimePowerLimitReduction
import RHFormalization.HalfPlaneGeometry

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Probe: chosen-length D overlap builder from the generic stage-split limit theorem,
assuming F/R use the same chosen alpha sequence as the chosen-length B-limit.
-/
theorem chosenLengthOverlapBuilder_of_alpha_aligned_probe
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (F : DFHLimitData finiteOperatorLayer.toStagePackage)
    (sectors : DResidualSectorData finiteOperatorLayer.toStagePackage)
    (sectorSplit :
      DResidualSectorSplitAPI finiteOperatorLayer.toStagePackage sectors)
    (sectorBounds :
      DResidualSectorBoundsAPI finiteOperatorLayer.toStagePackage sectors)
    (master :
      DMasterResidualAPI finiteOperatorLayer.toStagePackage sectors)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha :
      (master.h_master sectorSplit sectorBounds).alpha = S.alpha) :
    let Cshared :=
      SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S
    let finiteCanonicalLimit :=
      SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S
    let Bdata :=
      buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
        finiteOperatorLayer
        Cshared
        finiteCanonicalLimit
    let Rdata := master.h_master sectorSplit sectorBounds
    DOverlapIdentityAPI
      finiteOperatorLayer.toStagePackage
      Bdata
      F
      Rdata := by
  let Cshared :=
    SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S
  let finiteCanonicalLimit :=
    SharpCutoffChosenLengthFiniteCanonicalLimit finiteOperatorLayer S
  let Bdata :=
    buildDBcanLimitDataFromOperatorFiniteCanonicalLimit
      finiteOperatorLayer
      Cshared
      finiteCanonicalLimit
  let Blimit :=
    buildDOperatorPrimePowerLimitAtOverlapData_fromFiniteCanonicalLimit
      finiteOperatorLayer
      Cshared
      finiteCanonicalLimit
  let Rdata := master.h_master sectorSplit sectorBounds

  change
    DOverlapIdentityAPI
      finiteOperatorLayer.toStagePackage
      Bdata
      F
      Rdata

  refine
    DOverlapIdentityAPI_from_pointwise_stage_limits
      finiteOperatorLayer.toStageSplit
      ?hF
      ?hB
      ?hR

  · intro s hs
    exact
      DFHLimitData.pointwise_F_stage_tendsto_of_RHP_subset_Omega
        F
        (rightHalfPlane_subset_Omega
          finiteOperatorLayer.toStagePackage.sigma0
          hσ)
        s
        hs

  · intro s hs
    have hB_S :
        Filter.Tendsto
          (fun n : ℕ =>
            finiteOperatorLayer.toStagePackage.B_stage (S.alpha n) s)
          Filter.atTop
          (nhds (Bdata.Bcan s)) := by
      have hBlim := Blimit.h_B_stage_tendsto_Bcan s hs
      simpa [Blimit, Bdata, Cshared, finiteCanonicalLimit] using hBlim
    simpa [hF_alpha] using hB_S

  · intro s hs
    have hR0 :
        Filter.Tendsto
          (fun n : ℕ =>
            finiteOperatorLayer.toStagePackage.R_stage (Rdata.alpha n) s)
          Filter.atTop
          (nhds (Rdata.RH s)) :=
      DMasterResidualData.pointwise_R_stage_tendsto_of_RHP_subset_Omega
        Rdata
        (rightHalfPlane_subset_Omega
          finiteOperatorLayer.toStagePackage.sigma0
          hσ)
        s
        hs

    have hR_eq_F : Rdata.alpha = F.alpha := by
      calc
        Rdata.alpha = S.alpha := hR_alpha
        _ = F.alpha := hF_alpha.symm

    simpa [hR_eq_F] using hR0

end

end RHFormalization
