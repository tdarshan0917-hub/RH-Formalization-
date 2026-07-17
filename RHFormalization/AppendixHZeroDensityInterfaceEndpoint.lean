import RHFormalization.AppendixHInterfaceEndpoint
import RHFormalization.EnvelopeFromZeroDensity

/-!
# RHFormalization.AppendixHZeroDensityInterfaceEndpoint

This file packages the green Appendix-H interface endpoint with the already-built
zero-density-to-envelope constructor.

It gives the manuscript-facing closure shape:

  real-zero-freeness
  + zero-density summability
  + Appendix-H overlap identity
  => RH

No direct principal-part theorem for the raw displacement kernel is used here.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

#check RH_from_appendixH_interface_envelope
#check buildEnvelopeFromZeroDensity
#check RH_from_designed_D_zero_density

/--
Appendix-H interface endpoint with the zero-side envelope discharged from
the zero-density summability input `hsum`.

Remaining payload:
* real-zero-freeness;
* zero-density summability;
* Appendix-H archimedean package;
* Appendix-H overlap identity.
-/
theorem RH_from_appendixH_interface_zeroDensity
    (h_real_zero_free :
      ∀ s : ℂ,
        s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (Hpkg : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_appendixH_overlap :
      ∀ s : ℂ,
        s ∈ RightHalfPlane sigmaH →
          designedY.B.Cshared.Bshared s =
            Hpkg.Harch s - ZpoleSeries defaultZeroMultiplicityData s) :
    RiemannHypothesis :=
  RH_from_appendixH_interface_envelope
    h_real_zero_free
    (buildEnvelopeFromZeroDensity
      defaultZeroMultiplicityData
      hsum)
    Hpkg
    sigmaH
    hσH
    h_appendixH_overlap

#check RH_from_appendixH_interface_zeroDensity
#print axioms RH_from_appendixH_interface_zeroDensity

end

end RHFormalization
