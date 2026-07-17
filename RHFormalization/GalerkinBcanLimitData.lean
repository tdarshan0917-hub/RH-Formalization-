/-
GalerkinBcanLimitData.lean

DBcanLimitData for the genuine-operator stage package: the D-side limiting
prime package IS the genuine shifted-Laplace prime package at threshold 1 —
identity by rfl, sigma inequality banked in HonestEndpointV5. This pins the
D-export's Cshared to exactly what RH_from_DExportLayer demands.
-/
import RHFormalization.GalerkinStagePackage
import RHFormalization.HonestEndpointV5

namespace RHFormalization
noncomputable section

/-- The genuine D-side Bcan limit data: the prime tsum package itself. -/
def galerkinBcanLimitData : DBcanLimitData galerkinStagePackage :=
  { Bcan := (shiftedLaplacePrimePackageAt 1).Bshared
    Cshared := shiftedLaplacePrimePackageAt 1
    h_Cshared_sigma_le := by
      show (shiftedLaplacePrimePackageAt 1).sigma0 ≤ (1 : ℝ)
      exact shiftedLaplacePrime_sigma_le
    h_Bcan_matches_shared := fun _ _ => rfl }

/-- The Cshared slot is exactly what the V8 endpoint demands. -/
theorem galerkinBcanLimitData_Cshared :
    galerkinBcanLimitData.Cshared = shiftedLaplacePrimePackageAt 1 := rfl

#print axioms galerkinBcanLimitData
#print axioms galerkinBcanLimitData_Cshared

end
end RHFormalization
