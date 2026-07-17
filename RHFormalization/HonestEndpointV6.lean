/-
HonestEndpointV6.lean

ZF discharged: `h_real_zero_free` is a proven theorem (EtaPositivity.lean),
feeding `defaultZetaZeroFacts_of_realZeroFree`. The honest-route frontier is
now exactly TWO objects: D : OperatorResolventBridge and E : interface API.
-/
import RHFormalization.HonestEndpointV5
import RHFormalization.EtaPositivity
import RHFormalization.DefaultZetaZeroFacts

namespace RHFormalization

noncomputable section

/-- Proven zeta-zero facts: no hypotheses. -/
def provenZetaZeroFacts : ZetaZeroFacts :=
  defaultZetaZeroFacts_of_realZeroFree h_real_zero_free

/-- V6 endpoint: pillars (b), (c), (d) and ZF all internal.
Frontier = (D, E). -/
theorem RH_from_D_E
    (D : OperatorResolventBridge)
    (E : InterfaceBridgeNonnegativeAPI D
      (unconditionalX_from_overlap
        shiftedLaplaceOverlap).toLegacyZeroPolePackageAPI) :
    RiemannHypothesis :=
  RH_from_ZF_D_E provenZetaZeroFacts D E

#check @RH_from_D_E
#print axioms provenZetaZeroFacts
#print axioms RH_from_D_E

end
end RHFormalization
