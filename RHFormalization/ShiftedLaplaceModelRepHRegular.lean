import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.ShiftedLaplaceModelHRegular
import RHFormalization.ShiftedLaplaceModelHRegularProof
import RHFormalization.ShiftedLaplaceRepZpoleResidue
import RHFormalization.ShiftedLaplaceRepMeromorphic
import RHFormalization.EnvelopeFromZeroDensity
import RHFormalization.XiSummability
import RHFormalization.DefaultZeroMultiplicity
import RHFormalization.MeromorphyAssembly
import RHFormalization.ExplicitFormulaRegularBranch

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/-- The model Appendix-H function for the REP pole series:
`model + ZpoleRepSeries`. -/
abbrev shiftedLaplaceModelRepAppendixHFunction : ℂ → ℂ :=
  fun s : ℂ =>
    shiftedLaplaceLogDerivModel s
      + ZpoleRepSeries defaultZeroMultiplicityData s

/-- **`h_regular` for the model Rep function — free-standing.** The function
`model + ZpoleRepSeries` is holomorphic away from witnesses: the model by
`shiftedLaplaceModel_regular` (geometric gate), and `ZpoleRepSeries` by
`repZpole_analyticAt_nonpole` (with the envelope built from `hsum_unconditional`).
Unconditional. -/
theorem shiftedLaplaceModelRep_h_regular
    (ZF : ZetaZeroFacts) :
    ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC shiftedLaplaceModelRepAppendixHFunction z := by
  intro z hzΩ hznw
  have hmodel : AnalyticAt ℂ shiftedLaplaceLogDerivModel z :=
    shiftedLaplaceModel_regular z hzΩ hznw
  have hznp : z ∉ ZeroPoleSet :=
    not_zeroPoleSet_of_not_zeroWitness ZF z hzΩ hznw
  have hD : ZeroPoleEnvelopeData defaultZeroMultiplicityData :=
    buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional
  have hZ : AnalyticAt ℂ (ZpoleRepSeries defaultZeroMultiplicityData) z :=
    repZpole_analyticAt_nonpole defaultZeroMultiplicityData hD z hzΩ hznp
  show AnalyticAt ℂ (fun s => shiftedLaplaceLogDerivModel s
    + ZpoleRepSeries defaultZeroMultiplicityData s) z
  exact hmodel.add hZ

#print axioms shiftedLaplaceModelRep_h_regular

end
end RHFormalization
