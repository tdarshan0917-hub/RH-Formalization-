import RHFormalization.GlobalMeromorphicIdentity
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace RHFormalization

noncomputable section

open Complex

#check AnalyticAt.meromorphicAt
#check HasFPowerSeriesAt.meromorphicAt
#check HasFPowerSeriesWithinAt.hasFPowerSeriesAt
#check HasFPowerSeriesWithinAt.analyticAt
#check HasFPowerSeriesWithinAt.analyticWithinAt
#check AnalyticWithinAt.analyticAt
#check AnalyticOn.analyticAt
#check AnalyticOnNhd.meromorphicOn
#check MeromorphicOn.sub
#check MeromorphicOn.add

end

end RHFormalization
