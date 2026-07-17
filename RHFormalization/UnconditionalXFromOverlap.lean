/-
UnconditionalXFromOverlap.lean

X-assembly for the honest route. The blink layer fills every field of
`HMeromorphicPackageLayerV2` with zero-hypothesis banked objects except
`overlap` (pillar (d)'s entry point), which rides as the sole hypothesis.
The endpoint object `X : HMeromorphicWithNormalFormPoles` then feeds
`RH_from_manuscript_content`. No raw-Bshared statement appears here.
-/
import RHFormalization.RepBlinkConvergence
import RHFormalization.ShiftedLaplaceHarchOmegaAssembly
import RHFormalization.ShiftedLaplaceHarchOmegaWitness
import RHFormalization.DefaultPoleNormalFormLayer
import RHFormalization.PoleNormalForm

namespace RHFormalization

noncomputable section

/-- Coefficient collapse for the singleton grouped class. -/
theorem groupedResidueCoeff_default_singleton
    (M : ZeroMultiplicityData) (W : ZeroWitness) :
    groupedResidueCoeff M (defaultGroupedPoleClass M W) = (M.mult W.ρ : ℂ) := by
  simp [groupedResidueCoeff, groupedMultiplicitySum, defaultGroupedPoleClass]

/-- Genuine pole of the rep series at every witness: principal part with
coefficient `mult W.ρ`, nonzero by `h_mult_pos`. Zero hypotheses. -/
theorem repZpole_genuine_pole (W : ZeroWitness) :
    HasGenuinePole (ZpoleRepSeries defaultZeroMultiplicityData) W.s0 := by
  refine ⟨(defaultZeroMultiplicityData.mult W.ρ : ℂ), ?_, ?_⟩
  · exact_mod_cast
      (defaultZeroMultiplicityData.h_mult_pos W.ρ W.h_zero).ne'
  · exact zpoleRepSeries_pp_at_witness W

/-- The blink layer: every field zero-hypothesis except `overlap`. -/
def blinkLayerFromOverlap
    (overlap :
      HSideOverlapPackage
        (ZpoleRepSeries defaultZeroMultiplicityData)
        unconditionalHArchPackage.Harch) :
    HMeromorphicPackageLayerV2 :=
  { M := defaultZeroMultiplicityData
    E := repBlinkExhaustion
    Zpole := ZpoleRepSeries defaultZeroMultiplicityData
    convergence := repBlinkConvergenceAPI
    poleSeriesMeromorphic := repZpoleMeromorphicFromSeriesAPI_blink
    HarchPackage := unconditionalHArchPackage
    overlap := overlap
    h_genuine_poles := repZpole_genuine_pole }

/-- X-assembly: the overlap package (pillar (d) entry) is the sole input. -/
def unconditionalX_from_overlap
    (overlap :
      HSideOverlapPackage
        (ZpoleRepSeries defaultZeroMultiplicityData)
        unconditionalHArchPackage.Harch) :
    HMeromorphicWithNormalFormPoles :=
  { layer := blinkLayerFromOverlap overlap
    normalFormGroupedLayer :=
      buildHSideGroupedPoleNormalFormDataFromPrincipalParts
        (buildZeroPolePackageFromHMeromorphicLayer
          (blinkLayerFromOverlap overlap))
        defaultZeroMultiplicityData
        (fun W => by
          rw [groupedResidueCoeff_default_singleton]
          exact zpoleRepSeries_pp_at_witness W) }

#print axioms groupedResidueCoeff_default_singleton
#print axioms repZpole_genuine_pole
#print axioms unconditionalX_from_overlap

end
end RHFormalization
