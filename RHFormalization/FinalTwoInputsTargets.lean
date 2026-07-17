import RHFormalization.EtaPositivity
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.ZetaZeroCounting
import RHFormalization.HsumCertificate
import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.ExplicitFormulaBRegular
import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.RHFromTsumPrincipalPart
import RHFormalization.AppendixHOverlapFromLocalExtensions
import RHFormalization.AppendixHHoloClosure

namespace RHFormalization

/-
FINAL INPUT 1:
This is the zero-density / hsum target.
The previous audit showed `ZetaZeroDensityData` requires:
  enum
  enum_injective
  hsummable
So this theorem is the real hsum closure target.
-/
theorem hsum_default_TARGET
    (D : ZetaZeroDensityData defaultZeroMultiplicityData) :
    Summable fun ρ =>
      ↑(defaultZeroMultiplicityData.mult ↑ρ) / (1 + (↑ρ).im ^ 2) :=
  hsum_of_zeroDensityData defaultZeroMultiplicityData D

/-
FINAL INPUT 2:
This is the explicit-formula holomorphy target.
We are checking the available routes and their exact remaining inputs.
-/
#check designed_h_holo_from_localEF
#check designedY_Bshared_regular
#check Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
#check designed_h_holo_from_localExtensions
#check RH_from_tsum_principalPart
#check RH_from_designed_D_zero_density

/-
CAPSTONE:
Once hsum_default and h_holo_default are closed, this is the final theorem.
-/
theorem RH_unconditional_TARGET
    (hsum_default :
      Summable fun ρ =>
        ↑(defaultZeroMultiplicityData.mult ↑ρ) / (1 + (↑ρ).im ^ 2))
    (h_holo_default :
      HolomorphicOnC
        (fun s => designedY.B.Cshared.Bshared s + ZpoleSeries defaultZeroMultiplicityData s)
        Ω) :
    RiemannHypothesis :=
  RH_from_designed_D_zero_density
    h_real_zero_free
    hsum_default
    h_holo_default

#print axioms hsum_default_TARGET
#print axioms RH_unconditional_TARGET
#print axioms h_real_zero_free
#print axioms designed_h_holo_from_localEF
#print axioms designed_h_holo_from_localExtensions
#print axioms RH_from_designed_D_zero_density

end RHFormalization
