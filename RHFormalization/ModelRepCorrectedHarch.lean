import RHFormalization.ModelRepCorrectedHolo
import RHFormalization.ShiftedLaplaceRepCorrectedHarch
import RHFormalization.HExplicitFormulaSplitChosenCshared
import RHFormalization.ShiftedLaplaceModelPackageProbe
import RHFormalization.PoleGeometry
import RHFormalization.HMeromorphicPackage

namespace RHFormalization
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- The corrected Harch package built from the MODEL B-side. `Harch :=
genRepCorrectedGlobal model`, holomorphic on Ω with all inputs discharged
(`model_repCorrectedGlobal_holomorphicOn`). -/
noncomputable def modelRepCorrectedHarchPackage (ZF : ZetaZeroFacts) : HArchPackage :=
  { Harch := genRepCorrectedGlobal shiftedLaplaceLogDerivModel
    h_Harch_holo := model_repCorrectedGlobal_holomorphicOn ZF }

/-- Split for the model corrected Harch on the half-plane: on `RightHalfPlane
sigma0` (`0 ≤ sigma0`) there are no witnesses, so `genRepCorrectedGlobal model =
genRepRaw model = model + ZpoleRep`, giving `model = Harch - ZpoleRep`. -/
theorem modelRepCorrectedHarchPackage_split
    (ZF : ZetaZeroFacts) (sigma0 : ℝ) (hsigma : 0 ≤ sigma0)
    (s : ℂ) (hs : s ∈ RightHalfPlane sigma0) :
    (shiftedLaplaceModelPackageAt sigma0).Bshared s =
      (modelRepCorrectedHarchPackage ZF).Harch s
        - ZpoleRepSeries defaultZeroMultiplicityData s := by
  have hnp : s ∉ ZeroPoleSet :=
    notMem_zeroPoleSet_of_mem_rightHalfPlane hsigma hs
  show shiftedLaplaceLogDerivModel s =
      genRepCorrectedGlobal shiftedLaplaceLogDerivModel s
        - ZpoleRepSeries defaultZeroMultiplicityData s
  rw [genRepCorrectedGlobal_eq_raw_of_notMem shiftedLaplaceLogDerivModel hnp]
  show shiftedLaplaceLogDerivModel s =
      (shiftedLaplaceLogDerivModel s
        + ZpoleRepSeries defaultZeroMultiplicityData s)
        - ZpoleRepSeries defaultZeroMultiplicityData s
  ring

#print axioms modelRepCorrectedHarchPackage
#print axioms modelRepCorrectedHarchPackage_split

end
end RHFormalization
