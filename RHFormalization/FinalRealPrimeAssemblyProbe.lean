import RHFormalization.FinalRHAssembly
import RHFormalization.RealPrimeY
import RHFormalization.RealPrimeRHSharp
import RHFormalization.HMeromorphicWithNormalFormChosenCshared
import RHFormalization.ModelRepCorrectedHarch
import RHFormalization.DefaultPoleNormalFormLayer
import RHFormalization.ShiftedLaplaceWitnessCancellationFromPrincipalParts
import RHFormalization.ShiftedLaplaceTLUFromLocalMTest
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-
GOAL OF THIS FILE:
No new math.
No new branch.
Only answer:

  Which already-banked Y/close plugs into final_RH_assembly?

The expected endpoint is either:

  final_RH_assembly 1 Y hYC (by rfl)

or the safer chosen-Cshared close:

  finalRHSpine_from_HChosenDSharedC ... Y ... (C := Y.B.Cshared)

If this file fails, the compiler error is the true remaining assembly gap.
-/

#check final_RH_assembly
#check realPrimeY
#check realPrime_RH_sharp
#check finalRHSpine_from_HChosenDSharedC

-- First: print the exact shape Lean sees for the final pieces.
#print realPrimeY
#print final_RH_assembly
#print finalRHSpine_from_HChosenDSharedC

end
end RHFormalization
