import RHFormalization.PrimeSideAlignmentContract
import RHFormalization.PrimeSideOverlapAlignment
import RHFormalization.ExplicitFormulaHolomorphyFromRegular
import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.ExplicitFormulaBRegular

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/-!
Focused route-lock.

Goal: determine the exact existing theorem shape that can turn

  PrimeSideAlignmentContract.h_Btr_opposite_principalPart
  PrimeSideAlignmentContract.h_Btr_regular_away_from_witnesses

into

  HolomorphicOnC (fun s => A.Btr s + ZpoleSeries defaultZeroMultiplicityData s) Ω

without returning to the bad displacement-kernel branch.
-/

#check PrimeSideAlignmentContract
#check PrimeSideOverlapAlignment
#check RH_from_primeSideOverlapAlignment_designed_convergence

-- Existing local-cancellation / regular-branch machinery.
#check Harch_holomorphic_from_principalParts_and_Bregular
#print Harch_holomorphic_from_principalParts_and_Bregular

#check Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
#print Harch_holomorphic_from_tsumPrincipalParts_and_Bregular

#check regular_branch_from_Bregular
#print regular_branch_from_Bregular

#check designed_h_holo_from_localEF
#print designed_h_holo_from_localEF

-- Data wrappers around principal parts / regularity.
#check BsharedOppositePrincipalPartData
#print BsharedOppositePrincipalPartData

#check designedY_Bshared_regular
#check designedY_Bshared_holomorphicAt

-- Z-side principal parts and meromorphy from convergence.
#check zside_pair_principalPart_from_convergence
#check h_pp_from_convergence
#check meromorphicOn_from_convergence

end

end RHFormalization
