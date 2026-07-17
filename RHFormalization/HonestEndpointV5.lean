/-
HonestEndpointV5.lean

Pillar (d) discharged. The shared-model identity holds for the GENUINE
shifted-Laplace prime package at sigma0 = 1: banked
`shiftedLaplace_Bshared_eqOn_model` on the abs-conv region, plus the banked
containment `RightHalfPlane 1 ⊆ shiftedLaplaceAbsConvRegion`. The honest
route frontier is now exactly (ZF, D, E).
-/
import RHFormalization.OverlapFromModelIdentity
import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceSqrtReLowerBound

namespace RHFormalization

noncomputable section

/-- The genuine prime package satisfies the model identity on ℜs > 1. -/
theorem shiftedLaplacePrime_h_model :
    ∀ s ∈ RightHalfPlane 1,
      (shiftedLaplacePrimePackageAt 1).Bshared s =
        shiftedLaplaceLogDerivModel s :=
  fun s hs => shiftedLaplace_Bshared_eqOn_model 1 (rightHalfPlane_one_subset_shiftedLaplaceAbsConvRegion hs)

theorem shiftedLaplacePrime_sigma_le :
    (shiftedLaplacePrimePackageAt 1).sigma0 ≤ 1 := by
  first
    | exact le_refl 1
    | exact le_of_eq rfl
    | norm_num [shiftedLaplacePrimePackageAt,
        canonicalPrimePowerPackageFromKernelTsum]
    | simp [shiftedLaplacePrimePackageAt,
        canonicalPrimePowerPackageFromKernelTsum]

/-- The fully-discharged overlap package for the genuine prime package. -/
def shiftedLaplaceOverlap :
    HSideOverlapPackage
      (ZpoleRepSeries defaultZeroMultiplicityData)
      unconditionalHArchPackage.Harch :=
  overlapFromSharedModelIdentity
    (shiftedLaplacePrimePackageAt 1) 1
    (by norm_num)
    shiftedLaplacePrime_sigma_le
    shiftedLaplacePrime_h_model

/-- V5 endpoint: pillars (b), (c), (d) all internal. Frontier = (ZF, D, E). -/
theorem RH_from_ZF_D_E
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (E : InterfaceBridgeNonnegativeAPI D
      (unconditionalX_from_overlap
        shiftedLaplaceOverlap).toLegacyZeroPolePackageAPI) :
    RiemannHypothesis :=
  RH_from_overlap_D_E ZF D shiftedLaplaceOverlap E

#check @RH_from_ZF_D_E
#print axioms shiftedLaplaceOverlap
#print axioms RH_from_ZF_D_E

end
end RHFormalization
