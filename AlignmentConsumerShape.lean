import RHFormalization.PrimeSideAlignmentContract
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.ExplicitFormulaBRegular
import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.ExplicitFormulaRegularBranch
import RHFormalization.ExplicitPrimePackageIdentity

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/-!
This is not another model audit.

Goal: identify the exact theorem we should consume next so that
`PrimeSideAlignmentContract` can feed the RH spine through the correct
`Btr` / `D.B` route, instead of the paused displacement-kernel route.
-/

#check PrimeSideAlignmentContract
#check primeSideAlignmentContract_of_D_B

-- Earlier RH consumers. We want the one that still accepts an arbitrary Harch/split package.
#check RH_from_raw_inputs
#check RH_from_designed_D_convergence
#check RH_from_designed_D_convergence_only
#check RH_from_designed_D_zero_density
#check RH_from_designed_D_zero_density_localEF_noBregular

-- Harch package shape: needed to define Harch := Btr + Zpole.
#check HArchPackage
#print HArchPackage

-- Zero-side / convergence objects we will reuse.
#check ZpoleSeries
#check defaultZeroMultiplicityData
#check defaultZeroExhaustion
#check defaultZpoleConvFromZeroDensity
#check buildEnvelopeFromZeroDensity
#check zside_pair_principalPart_from_convergence

-- Existing explicit-formula lemmas. We need to know whether to generalize or bypass them.
#check designed_h_holo_from_localEF
#check Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
#check Harch_holomorphic_from_principalParts_and_Bregular
#check regular_branch_from_Bregular

-- D-side objects.
#check designedY.toOperatorResolventBridge
#check designedY_Bshared_regular
#check designedY_Bshared_holomorphicAt
#check designedY_Cshared_Bshared_eq_tsum_global

end

end RHFormalization
