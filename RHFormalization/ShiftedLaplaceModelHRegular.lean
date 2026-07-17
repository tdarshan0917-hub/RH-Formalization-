import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.ShiftedLaplaceModelPackageProbe
import RHFormalization.ShiftedLaplaceModelHRegularProof
import RHFormalization.ZpoleFromSeries
import RHFormalization.DefaultZeroMultiplicity
import RHFormalization.ShiftedLaplaceHoloLocalReduction
import RHFormalization.MeromorphyAssembly
import RHFormalization.ExplicitFormulaRegularBranch
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

abbrev shiftedLaplaceModelAppendixHFunction : ℂ → ℂ :=
  fun s : ℂ =>
    shiftedLaplaceLogDerivModel s
      + ZpoleSeries defaultZeroMultiplicityData s

/-- **The model Appendix-H function is holomorphic away from witnesses.**
Both summands are holomorphic there: the model by `shiftedLaplaceModel_regular`
(the geometric gate), and `ZpoleSeries` by `zpole_analyticAt_nonpole`. -/
theorem shiftedLaplaceModel_h_regular
    (ZF : ZetaZeroFacts)
    (conv : ZeroPoleLocalUniformConvergenceAPI
      defaultZeroMultiplicityData defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData)) :
    ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC shiftedLaplaceModelAppendixHFunction z := by
  intro z hzΩ hznw
  -- model holomorphic at z (our geometric gate)
  have hmodel : AnalyticAt ℂ shiftedLaplaceLogDerivModel z :=
    shiftedLaplaceModel_regular z hzΩ hznw
  -- z avoids the zero-pole set
  have hznp : z ∉ ZeroPoleSet :=
    not_zeroPoleSet_of_not_zeroWitness ZF z hzΩ hznw
  -- ZpoleSeries holomorphic at z
  have hZ : AnalyticAt ℂ (ZpoleSeries defaultZeroMultiplicityData) z :=
    zpole_analyticAt_nonpole defaultZeroMultiplicityData
      (ZpoleSeries defaultZeroMultiplicityData) conv z hzΩ hznp
  -- sum holomorphic
  show AnalyticAt ℂ (fun s => shiftedLaplaceLogDerivModel s
    + ZpoleSeries defaultZeroMultiplicityData s) z
  exact hmodel.add hZ

#print axioms shiftedLaplaceModel_h_regular

end
end RHFormalization
