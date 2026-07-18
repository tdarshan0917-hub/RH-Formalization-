import RHFormalization.MainTheoremFromRealZeroFreeDefaultAC
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace RHFormalization

noncomputable section

open Complex Set Filter

#check MeromorphicIdentityPrincipleAPI
#print MeromorphicIdentityPrincipleAPI

#check MeromorphicOn
#check MeromorphicAt
#check AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq

-- Candidate names. Unknown identifiers are verdicts, not regressions.
#check MeromorphicOn.eqOn_of_preconnected_of_eqOn
#check MeromorphicOn.eqOn_of_preconnected_of_eventuallyEq
#check MeromorphicOn.eqOn_of_preconnected
#check MeromorphicOn.eq_of_preconnected_of_eqOn
#check MeromorphicOn.eq_of_preconnected_of_eventuallyEq
#check MeromorphicAt.eventuallyEq_of_eqOn
#check MeromorphicOn.eventuallyEq_of_eqOn

/--
Shape probe only. This intentionally leaves a placeholder.
If a direct Mathlib theorem exists, the next patch should be one file.
If not, `I` is a genuine analytic API and should be parked.
-/
example
    (f g : ℂ → ℂ) (U V : Set ℂ)
    (hUconn : IsPreconnected U)
    (hVopen : IsOpen V)
    (hVnonempty : V.Nonempty)
    (hVU : V ⊆ U)
    (hf : MeromorphicOnC f U)
    (hg : MeromorphicOnC g U)
    (heq : Set.EqOn f g V) :
    Set.EqOn f g U := by
  exact ?meromorphic_identity_gap

end

end RHFormalization
