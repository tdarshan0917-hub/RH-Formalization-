import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.EnvelopeFromZeroDensity
import RHFormalization.ZpoleFromSeries

/-!
# RHFormalization.ExplicitFormulaLocalReduction

EF5: specialize the EF4 local-cancellation reduction to the actual V9 objects.

This is not a replacement for `CurrentFrontierEndpoint.lean`. It is a bridge
theorem showing that the V9 global holomorphy input can be replaced by three
local explicit-formula obligations:

1. concrete prime-power tsum opposite principal parts at witness points;
2. point-value compatibility at witness centers;
3. Bshared holomorphic at regular Ω-points.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
The zero-pole convergence API produced from the V9 zero-density summability
hypothesis.
-/
def defaultZpoleConvFromZeroDensity
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2))) :
    ZeroPoleLocalUniformConvergenceAPI
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleSeries defaultZeroMultiplicityData) :=
  buildZeroPoleLUCAPIFromEnvelope
    defaultZeroMultiplicityData
    (buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum)

/--
EF5 bridge: the V9 holomorphy input follows from the three local EF obligations.
-/
theorem designed_h_holo_from_localEF
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (ZF : ZetaZeroFacts)
    (h_tsum_principalPart :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC *
                (displacementCanonicalKernel (heatKernelG 1)) q.center s)
          W.s0
          (-(groupedResidueCoeff
              defaultZeroMultiplicityData
              (pairGroupedPoleClass defaultZeroMultiplicityData W))))
    (hpoint :
      ∀ W : ZeroWitness,
        let c : ℂ :=
          -(groupedResidueCoeff
              defaultZeroMultiplicityData
              (pairGroupedPoleClass defaultZeroMultiplicityData W))
        let hBreg :=
          Classical.choose
            ((designedY_BPP_pair_from_tsum
                defaultZeroMultiplicityData
                h_tsum_principalPart).h_Bshared_principalPart W)
        let hZreg :=
          Classical.choose
            (zside_pair_principalPart_from_convergence
              defaultZeroMultiplicityData
              (ZpoleSeries defaultZeroMultiplicityData)
              (defaultZpoleConvFromZeroDensity hsum)
              W)
        hBreg W.s0 + hZreg W.s0 =
          designedY.B.Cshared.Bshared W.s0 +
            ZpoleSeries defaultZeroMultiplicityData W.s0)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC designedY.B.Cshared.Bshared z) :
    HolomorphicOnC
      (fun s : ℂ =>
        designedY.B.Cshared.Bshared s +
          ZpoleSeries defaultZeroMultiplicityData s)
      Ω :=
  Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
    ZF
    defaultZeroMultiplicityData
    (ZpoleSeries defaultZeroMultiplicityData)
    (defaultZpoleConvFromZeroDensity hsum)
    h_tsum_principalPart
    hpoint
    hB_regular

/--
V9 with the global `h_holo` input replaced by the local explicit-formula
obligations.
-/
theorem RH_from_designed_D_zero_density_localEF
    (h_real_zero_free :
      ∀ s : ℂ,
        s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (h_tsum_principalPart :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC *
                (displacementCanonicalKernel (heatKernelG 1)) q.center s)
          W.s0
          (-(groupedResidueCoeff
              defaultZeroMultiplicityData
              (pairGroupedPoleClass defaultZeroMultiplicityData W))))
    (hpoint :
      ∀ W : ZeroWitness,
        let c : ℂ :=
          -(groupedResidueCoeff
              defaultZeroMultiplicityData
              (pairGroupedPoleClass defaultZeroMultiplicityData W))
        let hBreg :=
          Classical.choose
            ((designedY_BPP_pair_from_tsum
                defaultZeroMultiplicityData
                h_tsum_principalPart).h_Bshared_principalPart W)
        let hZreg :=
          Classical.choose
            (zside_pair_principalPart_from_convergence
              defaultZeroMultiplicityData
              (ZpoleSeries defaultZeroMultiplicityData)
              (defaultZpoleConvFromZeroDensity hsum)
              W)
        hBreg W.s0 + hZreg W.s0 =
          designedY.B.Cshared.Bshared W.s0 +
            ZpoleSeries defaultZeroMultiplicityData W.s0)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC designedY.B.Cshared.Bshared z) :
    RiemannHypothesis :=
  RH_from_designed_D_zero_density
    h_real_zero_free
    hsum
    (designed_h_holo_from_localEF
      hsum
      (defaultZetaZeroFacts_of_realZeroFree h_real_zero_free)
      h_tsum_principalPart
      hpoint
      hB_regular)

#print axioms defaultZpoleConvFromZeroDensity
#print axioms designed_h_holo_from_localEF
#print axioms RH_from_designed_D_zero_density_localEF

end

end RHFormalization
