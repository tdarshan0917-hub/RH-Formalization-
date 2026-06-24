import RHFormalization.ResolventOperatorLayer
import RHFormalization.DOperatorExport
import RHFormalization.ShiftedLaplaceModelPackageProbe

namespace RHFormalization
noncomputable section
open Complex Topology Filter

/-- Clean DBcan limit data over the REAL resolvent operator layer.
Built directly (Bcan := Cshared.Bshared), avoiding the fragile selected-builder
normalization path that previously introduced sorryAx. -/
noncomputable def resolventDBcanLimit :
    DBcanLimitData resolventOperatorLayer.toStagePackage :=
  { Bcan := (shiftedLaplaceModelPackageAt 1).Bshared
    Cshared := shiftedLaplaceModelPackageAt 1
    h_Cshared_sigma_le := by
      show (shiftedLaplaceModelPackageAt 1).sigma0 ≤
        resolventOperatorLayer.toStagePackage.sigma0
      have h1 : (shiftedLaplaceModelPackageAt 1).sigma0 = 1 := rfl
      have h2 : resolventOperatorLayer.toStagePackage.sigma0 = 1 := rfl
      rw [h1, h2]
    h_Bcan_matches_shared := by
      intro s hs
      rfl }

end
end RHFormalization
