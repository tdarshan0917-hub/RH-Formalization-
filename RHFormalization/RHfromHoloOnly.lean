import RHFormalization.TwoInputEndpointFromEta
import RHFormalization.XiSummability

/-!
# RH from a single remaining input

Both analytic pillars are now proven theorems:
* `h_real_zero_free` (EtaPositivity) — ζ ≠ 0 on the real segment (0,1).
* `hsum_unconditional` (XiSummability) — zero-density summability, via the
  Riemann–von Mangoldt O(n log n) count and Abel/L-series summability.

This collapses `RH_from_eta_zeroDensity_holo` to a SINGLE remaining input:
`h_holo`, the explicit-formula holomorphy of `Bshared + ZpoleSeries` on Ω.
-/

namespace RHFormalization

/-- **RH from the single remaining input.** Both the eta (real-zero-free) and the
zero-density summability pillars are discharged by proven theorems; only the
explicit-formula holomorphy `h_holo` remains. -/
theorem RH_from_holo_only
    (h_holo :
      HolomorphicOnC
        (fun s => designedY.B.Cshared.Bshared s +
          ZpoleSeries defaultZeroMultiplicityData s) Ω) :
    RiemannHypothesis :=
  RH_from_eta_zeroDensity_holo hsum_unconditional h_holo

#print axioms RH_from_holo_only

end RHFormalization
