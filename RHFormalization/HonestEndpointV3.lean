/-
HonestEndpointV3.lean

X eliminated from the endpoint signature. The honest route's official frontier
is now: (ZF, D : OperatorResolventBridge, overlap : HSideOverlapPackage
(rep series) (unconditional Harch), E : interface API) -> RiemannHypothesis.
All X-internals (convergence, meromorphy, normal form, genuine poles) are
zero-hypothesis banked objects. Pillar (d) enters only through `overlap`.
-/
import RHFormalization.HonestEndpointV2
import RHFormalization.UnconditionalXFromOverlap

namespace RHFormalization

noncomputable section

theorem RH_from_overlap_D_E
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (overlap :
      HSideOverlapPackage
        (ZpoleRepSeries defaultZeroMultiplicityData)
        unconditionalHArchPackage.Harch)
    (E : InterfaceBridgeNonnegativeAPI D
      (unconditionalX_from_overlap overlap).toLegacyZeroPolePackageAPI) :
    RiemannHypothesis :=
  RH_from_manuscript_content ZF D (unconditionalX_from_overlap overlap) E

#check @RH_from_overlap_D_E
#print axioms RH_from_overlap_D_E

end
end RHFormalization
