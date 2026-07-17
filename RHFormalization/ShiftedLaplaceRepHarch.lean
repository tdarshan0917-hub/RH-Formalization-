import RHFormalization.HExplicitFormulaSplitChosenCshared
import RHFormalization.ShiftedLaplaceRepZpoleResidue

namespace RHFormalization
noncomputable section
open Complex

def shiftedLaplaceRepHarchPackageFromHolo
    (sigma0 : ℝ)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          (shiftedLaplacePrimePackageAt sigma0).Bshared s
            + ZpoleRepSeries defaultZeroMultiplicityData s)
        Ω) :
    HArchPackage :=
  HarchPackageFromChosenCsharedAddZpole
    (shiftedLaplacePrimePackageAt sigma0)
    (ZpoleRepSeries defaultZeroMultiplicityData)
    h_holo

theorem shiftedLaplaceRepHarchPackageFromHolo_split
    (sigma0 : ℝ)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          (shiftedLaplacePrimePackageAt sigma0).Bshared s
            + ZpoleRepSeries defaultZeroMultiplicityData s)
        Ω)
    (s : ℂ) :
    s ∈ RightHalfPlane sigma0 →
      (shiftedLaplacePrimePackageAt sigma0).Bshared s =
        (shiftedLaplaceRepHarchPackageFromHolo sigma0 h_holo).Harch s
          - ZpoleRepSeries defaultZeroMultiplicityData s := by
  intro hs
  exact
    HarchPackageFromChosenCsharedAddZpole_split
      (shiftedLaplacePrimePackageAt sigma0)
      (ZpoleRepSeries defaultZeroMultiplicityData)
      h_holo sigma0 s hs

#print axioms shiftedLaplaceRepHarchPackageFromHolo
#print axioms shiftedLaplaceRepHarchPackageFromHolo_split

end
end RHFormalization
