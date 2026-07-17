import RHFormalization.AnalyticWrappers
import RHFormalization.HMeromorphicPackage
import RHFormalization.ZpoleFromSeries

namespace RHFormalization

open Filter Topology

/-- The elementary simple pole: `c/(s - z)` has principal part with residue `c` at `z`. -/
theorem hasPrincipalPart_const_div_sub (c z : ℂ) :
    HasPrincipalPartAtC (fun s : ℂ => c / (s - z)) z c := by
  refine ⟨fun _ => 0, analyticAt_const, ?_⟩
  filter_upwards with w
  intro _
  simp

end RHFormalization
