/-
HonestEndpointV8.lean

Endpoint chain closed onto the Appendix-D export interface. Given any
DExportLayer whose shared package is the genuine shifted-Laplace prime
package at threshold <= 1, RiemannHypothesis follows. The entire remaining
burden of the honest route is producing that export layer on the GENUINE
operator (H0 + V_pp): FH-holo + the two compact-local convergences
(h_F_stage_to_FH, h_R_stage_to_RH — the h_conv frontier).
-/
import RHFormalization.HonestEndpointV7
import RHFormalization.DOperatorExport

namespace RHFormalization

noncomputable section

/-- V8 endpoint: RH from a D-export layer carrying the genuine prime package. -/
theorem RH_from_DExportLayer
    (D : DExportLayer)
    (h_sigma : D.P.sigma0 ≤ 1)
    (hC : D.B.Cshared = shiftedLaplacePrimePackageAt 1) :
    RiemannHypothesis :=
  RH_from_D_with_prime_interface
    (buildOperatorResolventBridgeFromDExport D)
    h_sigma
    (fun s hs => by
      have hs' : s ∈ RightHalfPlane D.P.sigma0 := by
        show D.P.sigma0 < s.re
        exact lt_of_le_of_lt h_sigma hs
      have hm := D.B.h_Bcan_matches_shared s hs'
      show D.B.Bcan s = (shiftedLaplacePrimePackageAt 1).Bshared s
      rw [hm, hC])

#check @RH_from_DExportLayer
#print axioms RH_from_DExportLayer

end
end RHFormalization
