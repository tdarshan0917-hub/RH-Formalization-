import RHFormalization.PrimeSideAlignmentToHarch
import RHFormalization.CurrentFrontierEndpoint

/-!
# RHFormalization.PrimeSideAlignmentDesignedBridge

This file connects the alignment/Harch adapter to the designed D-side object.

The key bridge is:

  designedY.B.Cshared.Bshared = designedY.toOperatorResolventBridge.B

on the Appendix-D overlap.  Once this is available, the aligned Harch package
feeds directly into `RH_from_designed_D_convergence`, bypassing the paused
displacement-kernel principal-part branch.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
Designed Bshared equals the B-field of the exported operator bridge on the
D-overlap.

This should be exactly `DBcanLimitData.h_Bcan_matches_shared`, transported
through `buildOperatorResolventBridgeFromDExport`.
-/
theorem designedY_Cshared_Bshared_eq_operatorBridge_B_on_overlap :
    ∀ s : ℂ,
      s ∈ RightHalfPlane designedY.toOperatorResolventBridge.sigma0 →
        designedY.B.Cshared.Bshared s =
          designedY.toOperatorResolventBridge.B s := by
  intro s hs
  have hmatch :
      designedY.B.Bcan s = designedY.B.Cshared.Bshared s := by
    exact designedY.B.h_Bcan_matches_shared s (by
      simpa [
        DDetailedConstructionWithOperatorLegality.toOperatorResolventBridge,
        DDetailedConstructionLayer.toOperatorResolventBridge,
        DDetailedConstructionLayer.toDExportLayer,
        buildOperatorResolventBridgeFromDExport
      ] using hs)
  simpa [
    DDetailedConstructionWithOperatorLegality.toOperatorResolventBridge,
    DDetailedConstructionLayer.toOperatorResolventBridge,
    DDetailedConstructionLayer.toDExportLayer,
    buildOperatorResolventBridgeFromDExport
  ] using hmatch.symm

/--
The aligned Harch package gives the exact split required by
`RH_from_designed_D_convergence`.
-/
theorem alignedHarch_split_for_designedY
    (A :
      PrimeSideAlignmentContract
        defaultZeroMultiplicityData
        designedY.toOperatorResolventBridge)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          A.Btr s + ZpoleSeries defaultZeroMultiplicityData s)
        Ω) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane designedY.toOperatorResolventBridge.sigma0 →
        designedY.B.Cshared.Bshared s =
          (alignedHarchPackage
            defaultZeroMultiplicityData
            designedY.toOperatorResolventBridge
            A
            h_holo).Harch s
            - ZpoleSeries defaultZeroMultiplicityData s :=
  alignedHarch_split_for_Btarget_on_D_overlap
    defaultZeroMultiplicityData
    designedY.toOperatorResolventBridge
    A
    h_holo
    designedY.B.Cshared.Bshared
    designedY_Cshared_Bshared_eq_operatorBridge_B_on_overlap

/--
Consumer theorem: RH from the corrected prime-side alignment route.

This deliberately avoids the paused theorem whose input is a principal-part
claim for the constant displacement kernel.
-/
theorem RH_from_primeSideAlignment_designed_convergence
    (h_real_zero_free :
      ∀ s : ℂ,
        s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI
        defaultZeroMultiplicityData
        defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI
        defaultZeroMultiplicityData
        defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (A :
      PrimeSideAlignmentContract
        defaultZeroMultiplicityData
        designedY.toOperatorResolventBridge)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          A.Btr s + ZpoleSeries defaultZeroMultiplicityData s)
        Ω)
    (hσ :
      0 ≤ designedY.toOperatorResolventBridge.sigma0) :
    RiemannHypothesis :=
  RH_from_designed_D_convergence
    h_real_zero_free
    (ZpoleSeries defaultZeroMultiplicityData)
    convergence
    poleSeriesMeromorphic
    (alignedHarchPackage
      defaultZeroMultiplicityData
      designedY.toOperatorResolventBridge
      A
      h_holo)
    designedY.toOperatorResolventBridge.sigma0
    hσ
    (alignedHarch_split_for_designedY A h_holo)

#check designedY_Cshared_Bshared_eq_operatorBridge_B_on_overlap
#check alignedHarch_split_for_designedY
#check RH_from_primeSideAlignment_designed_convergence
#print axioms RH_from_primeSideAlignment_designed_convergence

end

end RHFormalization
