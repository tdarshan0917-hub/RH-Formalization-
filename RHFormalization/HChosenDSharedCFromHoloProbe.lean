import RHFormalization.HMeromorphicWithNormalFormChosenCshared
import RHFormalization.HExplicitFormulaSplitChosenCshared
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
import RHFormalization.DefaultPoleNormalFormLayer

namespace RHFormalization

noncomputable section

def Denv_holo_probe :=
  buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum_unconditional

def conv_holo_probe :
    ZeroPoleLocalUniformConvergenceAPI
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData) :=
  buildZeroPoleLUCAPIFromEnvelope defaultZeroMultiplicityData Denv_holo_probe

def poleMero_holo_probe :
    ZpoleMeromorphicFromSeriesAPI
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData) :=
  { h_meromorphic := fun convergence hgp =>
      meromorphicOn_from_convergence
        defaultZeroMultiplicityData
        (ZpoleSeries defaultZeroMultiplicityData)
        convergence
        hgp }

def hpp_holo_probe :
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
      conv_holo_probe
      W

def hgp_holo_probe :
    ∀ W : ZeroWitness,
      HasGenuinePole (ZpoleSeries defaultZeroMultiplicityData) W.s0 :=
  fun W =>
    ⟨groupedResidueCoeff defaultZeroMultiplicityData
        (pairGroupedPoleClass defaultZeroMultiplicityData W),
      groupedResidueCoeff_ne_zero defaultZeroMultiplicityData W
        (pairGroupedPoleClass defaultZeroMultiplicityData W),
      hpp_holo_probe W⟩

theorem HChosenDSharedC_from_holo_probe
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          designedY.B.Cshared.Bshared s
            + ZpoleSeries defaultZeroMultiplicityData s)
        Ω) :
    RiemannHypothesis := by
  let HarchPackage :=
    HarchPackageFromChosenCsharedAddZpole
      designedY.B.Cshared
      (ZpoleSeries defaultZeroMultiplicityData)
      h_holo

  let sigma0 := designedY.B.Cshared.sigma0

  have h_Cshared_sigma_le : designedY.B.Cshared.sigma0 ≤ sigma0 := by
    rfl

  have h_split :
      ∀ s : ℂ,
        s ∈ RightHalfPlane sigma0 →
          designedY.B.Cshared.Bshared s =
            HarchPackage.Harch s
              - ZpoleSeries defaultZeroMultiplicityData s := by
    simpa [HarchPackage, sigma0] using
      HarchPackageFromChosenCsharedAddZpole_split
        designedY.B.Cshared
        (ZpoleSeries defaultZeroMultiplicityData)
        h_holo
        sigma0

  refine
    finalRHSpine_from_HChosenDSharedC
      (defaultZetaZeroFacts_of_realZeroFree h_real_zero_free)
      designedY
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData)
      conv_holo_probe
      poleMero_holo_probe
      HarchPackage
      sigma0
      h_Cshared_sigma_le
      h_split
      hgp_holo_probe
      ?normalFormGroupedLayer

  exact
    buildHSideGroupedPoleNormalFormDataFromPrincipalPartsPair
      _
      defaultZeroMultiplicityData
      hpp_holo_probe

#print axioms HChosenDSharedC_from_holo_probe

end
end RHFormalization
