import RHFormalization.ShiftedLaplaceRepHSideProviders
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric
open scoped Classical

/-
Direct corrected Rep zero-pole package and normal-form layer.

No fake representative ZeroExhaustion.
No old ZpoleSeries convergence.
No reflection-pair coefficient mismatch.

For ZpoleRepSeries the local principal coefficient is the singleton
representative coefficient `zetaZeroMult W.ρ`.
-/

def repSingletonGroupedPoleClass
    (W : ZeroWitness) :
    GroupedPoleClass defaultZeroMultiplicityData W :=
  { zeros := {W.ρ}
    h_witness_mem := by simp
    h_all_zeros := by
      intro ρ hρ
      have hρeq : ρ = W.ρ := by
        simpa using hρ
      rw [hρeq]
      exact W.h_zero
    h_same_pole := by
      intro ρ hρ
      have hρeq : ρ = W.ρ := by simpa using hρ
      rw [hρeq]
      exact W.hs0_def.symm }

theorem groupedResidueCoeff_repSingleton
    (W : ZeroWitness) :
    groupedResidueCoeff defaultZeroMultiplicityData
        (repSingletonGroupedPoleClass W)
      =
      ((zetaZeroMult W.ρ : ℕ) : ℂ) := by
  unfold groupedResidueCoeff groupedMultiplicitySum repSingletonGroupedPoleClass
  simp [defaultZeroMultiplicityData]

noncomputable def shiftedLaplaceRepZeroPolePackageDirect
    (ZF : ZetaZeroFacts)
    (hBpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
          W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (repRaw 1) z) :
    ZeroPolePackageAPI :=
  ZeroPolePackageAPI.mk
    (ZpoleRepSeries defaultZeroMultiplicityData)
    (shiftedLaplaceRepCorrectedHarchPackage
      1 ZF hBpp shiftedLaplace_hZpp_rep_provider h_regular).Harch
    (shiftedLaplacePrimePackageAt 1).Bshared
    1
    ZpoleRepSeries_meromorphicOn_Omega_direct
    (shiftedLaplaceRepCorrectedHarchPackage
      1 ZF hBpp shiftedLaplace_hZpp_rep_provider h_regular).h_Harch_holo
    (by
      intro s hs
      exact
        shiftedLaplaceRepCorrectedHarchPackage_split
          1 ZF (by norm_num)
          hBpp
          shiftedLaplace_hZpp_rep_provider
          h_regular
          s hs)

noncomputable def shiftedLaplaceRepNormalFormGroupedLayerDirect
    (ZF : ZetaZeroFacts)
    (hBpp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s => (shiftedLaplacePrimePackageAt 1).Bshared s)
          W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (repRaw 1) z) :
    HSideGroupedPoleNormalFormData
      (shiftedLaplaceRepZeroPolePackageDirect ZF hBpp h_regular) :=
  { M := defaultZeroMultiplicityData
    groupedClass := repSingletonGroupedPoleClass
    h_principalPart := by
      intro W
      rw [groupedResidueCoeff_repSingleton W]
      exact shiftedLaplace_hZpp_rep_provider W
    poleNormalForm := defaultPoleNormalFormLayer }

#print axioms repSingletonGroupedPoleClass
#print axioms groupedResidueCoeff_repSingleton
#print axioms shiftedLaplaceRepZeroPolePackageDirect
#print axioms shiftedLaplaceRepNormalFormGroupedLayerDirect

end
end RHFormalization
