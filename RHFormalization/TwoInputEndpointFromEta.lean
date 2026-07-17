import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.EtaPositivity

/-!
# RHFormalization.TwoInputEndpointFromEta

The eta track is complete: `RHFormalization.h_real_zero_free` (in `EtaPositivity.lean`)
is now a *proven theorem* — ζ ≠ 0 on the real segment (0,1), standard axioms, no `sorry`.

This file does NOT edit any canonical endpoint. It plugs the proven eta theorem into the
existing `RH_from_designed_D_zero_density` spine, discharging hypothesis (1) and exposing
the two genuinely remaining inputs: `hsum` (zero-density summability) and `h_holo`
(holomorphy of `Bshared + ZpoleSeries` on Ω).
-/

namespace RHFormalization

/-- RH from the two remaining inputs, after the eta track closes hypothesis (1).
`h_real_zero_free` is now supplied by the proven theorem, not assumed. -/
theorem RH_from_eta_zeroDensity_holo
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)))
    (h_holo :
      HolomorphicOnC
        (fun s => designedY.B.Cshared.Bshared s +
          ZpoleSeries defaultZeroMultiplicityData s) Ω) :
    RiemannHypothesis :=
  RH_from_designed_D_zero_density h_real_zero_free hsum h_holo

#print axioms RH_from_eta_zeroDensity_holo

end RHFormalization
