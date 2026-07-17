import RHFormalization.ShiftedLaplaceCapstoneTLU
import RHFormalization.XiSummability
import RHFormalization.EtaPositivity
import RHFormalization.EnvelopeFromZeroDensity
import RHFormalization.ZpoleFromSeries
import RHFormalization.MeromorphyAssembly
import RHFormalization.HPPEndgame
import RHFormalization.HSideResidueArithmetic
import RHFormalization.DefaultPoleNormalFormLayer

namespace RHFormalization
noncomputable section
open Complex Filter Topology

theorem final_RH_assembly
    (sigma0 : ℝ)
    (Y : DDetailedConstructionWithOperatorLegality)
    (hYC : Y.B.Cshared = shiftedLaplacePrimePackageAt sigma0)
    (h_Cshared_sigma_le : (shiftedLaplacePrimePackageAt sigma0).sigma0 ≤ sigma0) :
    RiemannHypothesis :=
  RH_from_shiftedLaplace_cancellation
    sigma0 Y hYC
    (buildZeroPoleLUCAPIFromEnvelope defaultZeroMultiplicityData
      (buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional))
    { h_meromorphic := fun convergence _ =>
        meromorphicOn_from_convergence defaultZeroMultiplicityData
          (ZpoleSeries defaultZeroMultiplicityData) convergence }
    (fun W =>
      ⟨groupedResidueCoeff defaultZeroMultiplicityData
          (pairGroupedPoleClass defaultZeroMultiplicityData W),
        groupedResidueCoeff_ne_zero defaultZeroMultiplicityData W
          (pairGroupedPoleClass defaultZeroMultiplicityData W),
        h_pp_from_convergence defaultZeroMultiplicityData
          (ZpoleSeries defaultZeroMultiplicityData)
          (buildZeroPoleLUCAPIFromEnvelope defaultZeroMultiplicityData
            (buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional)) W⟩)
    h_Cshared_sigma_le
    hsum_unconditional
    (defaultZetaZeroFacts_of_realZeroFree h_real_zero_free)
    ?hcancel ?h_tlu ?normalFormGroupedLayer
end
end RHFormalization
