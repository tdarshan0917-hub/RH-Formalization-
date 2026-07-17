/-
Pillar (c): the honest Appendix-H archimedean function on Ω — REP VERSION.

HarchΩ := shiftedLaplaceLogDerivModel + ZpoleRepSeries defaultZeroMultiplicityData

The rep series (one representative per reflection pair, re < 1/2) is the correct
partner: exactly one +mult pole per pole point, cancelling the model's −mult.
Firewall-compliant. Harch − ZpoleRep = model definitionally, so pillar (d)
reduces to the half-plane identity Bshared = model.
-/
import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.ShiftedLaplaceRepZpoleResidue
import RHFormalization.HMeromorphicPackage
import RHFormalization.DefaultZeroMultiplicity

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

/-- The honest Appendix-H archimedean candidate on Ω:
continued log-derivative model plus the representative zero-pole series. -/
noncomputable def shiftedLaplaceHarchOmega (s : ℂ) : ℂ :=
  shiftedLaplaceLogDerivModel s
    + ZpoleRepSeries defaultZeroMultiplicityData s

/-- Pillar-(d) reduction, definitional: `Harch − ZpoleRep = model` everywhere. -/
theorem shiftedLaplaceHarchOmega_sub_Zpole_eq_model (s : ℂ) :
    shiftedLaplaceHarchOmega s
      - ZpoleRepSeries defaultZeroMultiplicityData s
      = shiftedLaplaceLogDerivModel s := by
  unfold shiftedLaplaceHarchOmega
  ring

/-- Pointwise glue: wherever both pieces are analytic, `HarchΩ` is analytic. -/
theorem shiftedLaplaceHarchOmega_analyticAt
    {z : ℂ}
    (hmodel : AnalyticAt ℂ shiftedLaplaceLogDerivModel z)
    (hZ : AnalyticAt ℂ (ZpoleRepSeries defaultZeroMultiplicityData) z) :
    AnalyticAt ℂ shiftedLaplaceHarchOmega z := by
  unfold shiftedLaplaceHarchOmega
  exact hmodel.add hZ

/-- Package adapter: pillar (c) closes into the X-structure slot the moment
`HolomorphicOnC shiftedLaplaceHarchOmega Ω` is proved. -/
def harchPackageFromHarchOmega
    (h_holo : HolomorphicOnC shiftedLaplaceHarchOmega Ω) :
    HArchPackage :=
{ Harch := shiftedLaplaceHarchOmega
  h_Harch_holo := h_holo }

#print axioms shiftedLaplaceHarchOmega_sub_Zpole_eq_model
#print axioms shiftedLaplaceHarchOmega_analyticAt

end

end RHFormalization
