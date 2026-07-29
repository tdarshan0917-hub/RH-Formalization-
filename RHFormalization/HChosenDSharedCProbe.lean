import RHFormalization.HMeromorphicWithNormalFormChosenCshared
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.EtaPositivity
import RHFormalization.DefaultZetaZeroFacts
import RHFormalization.DesignedDetailedConstruction
import RHFormalization.DefaultZeroMultiplicity
import RHFormalization.DefaultZeroExhaustion
import RHFormalization.ZpoleFromSeries
import RHFormalization.EnvelopeFromZeroDensity
import RHFormalization.XiSummability
import RHFormalization.MeromorphyAssembly
import RHFormalization.HPPEndgame
import RHFormalization.ReflectionPairPoleClass
import RHFormalization.HExplicitFormulaSplitChosenCshared
import RHFormalization.DefaultPoleNormalFormLayer

namespace RHFormalization

noncomputable section

def Denv :=
  buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional

def conv_default :
    ZeroPoleLocalUniformConvergenceAPI
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData) :=
  buildZeroPoleLUCAPIFromEnvelope defaultZeroMultiplicityData Denv

def poleMero_default :
    ZpoleMeromorphicFromSeriesAPI
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData) :=
  { h_meromorphic := fun convergence hgp =>
      meromorphicOn_from_convergence
        defaultZeroMultiplicityData
        defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData)
        convergence
        hgp }

def hpp_default :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (ZpoleSeries defaultZeroMultiplicityData)
        W.s0
        (groupedResidueCoeff defaultZeroMultiplicityData
          (pairGroupedPoleClass defaultZeroMultiplicityData W)) :=
  fun W =>
    h_pp_from_convergence
      defaultZeroMultiplicityData
      (ZpoleSeries defaultZeroMultiplicityData)
      conv_default
      W

def hgp_default :
    ∀ W : ZeroWitness,
      HasGenuinePole (ZpoleSeries defaultZeroMultiplicityData) W.s0 :=
  fun W =>
    ⟨groupedResidueCoeff defaultZeroMultiplicityData
        (pairGroupedPoleClass defaultZeroMultiplicityData W),
      groupedResidueCoeff_ne_zero defaultZeroMultiplicityData W
        (pairGroupedPoleClass defaultZeroMultiplicityData W),
      hpp_default W⟩

def normalForm_default :
    HSideGroupedPoleNormalFormData
      (buildZeroPolePackageFromHMeromorphicLayer
        (buildHMeromorphicPackageLayerWithChosenCshared
          defaultZeroMultiplicityData
          defaultZeroExhaustion
          (ZpoleSeries defaultZeroMultiplicityData)
          conv_default
          poleMero_default
          ?HarchPackage
          designedY.B.Cshared
          ?sigma0
          ?h_Cshared_sigma_le
          ?h_split
          hgp_default)) :=
  buildHSideGroupedPoleNormalFormDataFromPrincipalPartsPair
    _
    defaultZeroMultiplicityData
    hpp_default

theorem HChosenDSharedC_probe : RiemannHypothesis := by
  refine
    finalRHSpine_from_HChosenDSharedC
      (defaultZetaZeroFacts_of_realZeroFree h_real_zero_free)
      designedY
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData)
      conv_default
      poleMero_default
      ?HarchPackage
      ?sigma0
      ?h_Cshared_sigma_le
      ?h_split
      hgp_default
      ?normalFormGroupedLayer

end
end RHFormalization
