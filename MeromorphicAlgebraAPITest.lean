import RHFormalization.GlobalMeromorphicIdentity
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.Basic

namespace RHFormalization

noncomputable section

#check MeromorphicAlgebraAPI
#check MeromorphicOn.add
#check MeromorphicOn.sub

#print MeromorphicAlgebraAPI
#print HolomorphicOnC
#print MeromorphicOnC

/--
Scratch target: can we build `MeromorphicAlgebraAPI` from existing local definitions?
This file is intentionally allowed to fail; the error tells us whether A is easy.
-/
def testMeromorphicAlgebraAPI : MeromorphicAlgebraAPI where
  h_holomorphic_to_meromorphic := by
    intro f U hU hf
    -- if HolomorphicOnC/MeromorphicOnC are aliases, this should be close to a Mathlib theorem;
    -- if they are abstract, Lean will expose the missing bridge here.
    exact ?h_hol_to_mer
  h_holomorphic_sub_meromorphic := by
    intro f g U hU hf hg
    -- if definitions align, use MeromorphicOn.sub after converting hf to meromorphic.
    exact ?h_sub

end

end RHFormalization
