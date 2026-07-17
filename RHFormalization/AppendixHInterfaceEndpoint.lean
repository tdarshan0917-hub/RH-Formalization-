import RHFormalization.CurrentFrontierEndpoint

/-!
# RHFormalization.AppendixHInterfaceEndpoint

Correct Appendix-H interface wrapper.

The previous attempt incorrectly passed `hsum` directly to
`RH_from_designed_D_summable`.

In this repo, `RH_from_designed_D_summable` consumes the already-built
zero-pole envelope object:

  D : ZeroPoleEnvelopeData defaultZeroMultiplicityData

So this file states the Appendix-H overlap identity in the manuscript shape
and routes through the existing green endpoint without changing the proof spine.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

#check RH_from_designed_D_summable
#check ZeroPoleEnvelopeData
#check HArchPackage
#check ZpoleSeries
#check defaultZeroMultiplicityData

/--
Appendix-H interface endpoint in the current repo's correct shape.

Remaining payload:
* real-zero-freeness;
* the zero-pole envelope object `D`;
* an Appendix-H archimedean package `Hpkg`;
* the Appendix-H overlap identity

    Bshared = Harch - ZpoleSeries

  on a right half-plane.
-/
theorem RH_from_appendixH_interface_envelope
    (h_real_zero_free :
      ∀ s : ℂ,
        s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (D : ZeroPoleEnvelopeData defaultZeroMultiplicityData)
    (Hpkg : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_appendixH_overlap :
      ∀ s : ℂ,
        s ∈ RightHalfPlane sigmaH →
          designedY.B.Cshared.Bshared s =
            Hpkg.Harch s - ZpoleSeries defaultZeroMultiplicityData s) :
    RiemannHypothesis :=
  RH_from_designed_D_summable
    h_real_zero_free
    D
    Hpkg
    sigmaH
    hσH
    h_appendixH_overlap

#check RH_from_appendixH_interface_envelope
#print axioms RH_from_appendixH_interface_envelope

end

end RHFormalization
