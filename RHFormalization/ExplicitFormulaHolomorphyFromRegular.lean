import RHFormalization.ExplicitFormulaRegularBranch

/-!
# RHFormalization.ExplicitFormulaHolomorphyFromRegular

EF3: assemble the explicit-formula holomorphy reduction.

This is not a new RH endpoint. It combines:

* the witness-branch theorem from principal parts; and
* the regular-branch theorem just banked in `ExplicitFormulaRegularBranch`.

The result reduces global holomorphy of `Bshared + Zpole` on Ω to:

1. B-side principal parts at witnesses;
2. Z-side principal parts at witnesses;
3. point-value compatibility at witnesses;
4. B-side holomorphy at regular points.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
Global holomorphy of `Y.B.Cshared.Bshared + Zpole` from witness principal
parts plus B-side regular holomorphy.

The Z-side regular holomorphy away from the pole set is supplied by the already
banked `regular_branch_from_Bregular`.
-/
theorem Harch_holomorphic_from_principalParts_and_Bregular
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (M : ZeroMultiplicityData)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (groupedClass :
      ∀ W : ZeroWitness, GroupedPoleClass M W)
    (hB :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          Y.B.Cshared.Bshared
          W.s0
          (-(groupedResidueCoeff M (groupedClass W))))
    (hZ :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          Zpole
          W.s0
          (- (-(groupedResidueCoeff M (groupedClass W)))))
    (hpoint :
      ∀ W : ZeroWitness,
        let c : ℂ := -(groupedResidueCoeff M (groupedClass W))
        let hBreg := Classical.choose (hB W)
        let hZreg := Classical.choose (hZ W)
        hBreg W.s0 + hZreg W.s0 =
          Y.B.Cshared.Bshared W.s0 + Zpole W.s0)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC Y.B.Cshared.Bshared z) :
    HolomorphicOnC
      (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
      Ω :=
  Harch_holomorphic_from_principalParts_and_regular
    Y
    Zpole
    M
    groupedClass
    hB
    hZ
    hpoint
    (regular_branch_from_Bregular
      ZF
      Y
      M
      Zpole
      conv
      hB_regular)

#print axioms Harch_holomorphic_from_principalParts_and_Bregular

end

end RHFormalization
