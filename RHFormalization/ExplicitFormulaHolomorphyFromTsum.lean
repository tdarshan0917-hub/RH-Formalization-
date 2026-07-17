import RHFormalization.ExplicitFormulaHolomorphyFromRegular
import RHFormalization.ExplicitPrimePackageIdentity

/-!
# RHFormalization.ExplicitFormulaHolomorphyFromTsum

EF4: specialize the explicit-formula holomorphy reduction to the concrete
prime-power tsum.

This is not a new RH endpoint. It removes two intermediate abstract inputs
from the explicit-formula branch:

* the B-side opposite-principal-part data is obtained from the concrete
  prime-power tsum principal-part theorem;
* the Z-side principal parts are obtained from the already-banked
  `h_pp_from_convergence`.

After this file, the explicit-formula holomorphy input is reduced to:

1. concrete prime-power tsum opposite principal parts at witness pole points;
2. point-value compatibility at witness centers;
3. regular-point holomorphy of the B-side.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
For the designed construction, concrete prime-power tsum principal parts imply
the B-side opposite-principal-part data with the honest reflection-pair residue.
-/
def designedY_BPP_pair_from_tsum
    (M : ZeroMultiplicityData)
    (h_tsum_principalPart :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC *
                (displacementCanonicalKernel (heatKernelG 1)) q.center s)
          W.s0
          (-(groupedResidueCoeff M (pairGroupedPoleClass M W)))) :
    BsharedOppositePrincipalPartData designedY M :=
  designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts
    M
    (pairGroupedPoleClass M)
    h_tsum_principalPart

/--
The Z-side principal part needed by the local-cancellation theorem is exactly
the already-derived principal-part theorem `h_pp_from_convergence`, with the
double negation normalized.
-/
theorem zside_pair_principalPart_from_convergence
    (M : ZeroMultiplicityData)
    (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (W : ZeroWitness) :
    HasPrincipalPartAtC
      Zpole
      W.s0
      (- (-(groupedResidueCoeff M (pairGroupedPoleClass M W)))) := by
  simpa using h_pp_from_convergence M Zpole conv W

/--
EF4: global holomorphy of `designedY.B.Cshared.Bshared + Zpole` follows from:

* concrete prime-power tsum opposite principal parts;
* point-value compatibility at witness centers;
* B-side holomorphy at regular Ω-points.

The Z-side principal parts are supplied by `h_pp_from_convergence`.
-/
theorem Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
    (ZF : ZetaZeroFacts)
    (M : ZeroMultiplicityData)
    (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (h_tsum_principalPart :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC *
                (displacementCanonicalKernel (heatKernelG 1)) q.center s)
          W.s0
          (-(groupedResidueCoeff M (pairGroupedPoleClass M W))))
    (hpoint :
      ∀ W : ZeroWitness,
        let c : ℂ := -(groupedResidueCoeff M (pairGroupedPoleClass M W))
        let hBreg :=
          Classical.choose
            ((designedY_BPP_pair_from_tsum M h_tsum_principalPart).h_Bshared_principalPart W)
        let hZreg :=
          Classical.choose
            (zside_pair_principalPart_from_convergence M Zpole conv W)
        hBreg W.s0 + hZreg W.s0 =
          designedY.B.Cshared.Bshared W.s0 + Zpole W.s0)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC designedY.B.Cshared.Bshared z) :
    HolomorphicOnC
      (fun s : ℂ => designedY.B.Cshared.Bshared s + Zpole s)
      Ω :=
  Harch_holomorphic_from_principalParts_and_Bregular
    ZF
    designedY
    Zpole
    M
    conv
    (pairGroupedPoleClass M)
    (designedY_BPP_pair_from_tsum M h_tsum_principalPart).h_Bshared_principalPart
    (zside_pair_principalPart_from_convergence M Zpole conv)
    hpoint
    hB_regular

#print axioms designedY_BPP_pair_from_tsum
#print axioms zside_pair_principalPart_from_convergence
#print axioms Harch_holomorphic_from_tsumPrincipalParts_and_Bregular

end

end RHFormalization
