import RHFormalization.ExplicitFormulaHolomorphyFromTsum
import RHFormalization.AppendixHHoloClosure

/-!
# RHFormalization.RHFromTsumPrincipalPart

The tightest honest manifest. `RiemannHypothesis` is assembled from:
* `h_real_zero_free`, `hsum` — the two classical inputs;
* `ZF : ZetaZeroFacts`, `conv` — structural data (zero facts, convergence);
* `h_tsum_principalPart` — THE analytic heart (prime-power displacement series'
  principal part at each witness = minus the zero-side residue);
* `hpoint`, `hB_regular` — the two residual local-compatibility obligations.

`Harch_holomorphic_from_tsumPrincipalParts_and_Bregular` turns these into the
`h_holo` consumed by the clean capstone `RH_from_appendixH_interface_zeroDensity_holo`.
This file does no new mathematics; it names the exact frontier in one statement.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex

theorem RH_from_tsum_principalPart
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hsum :
      Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
        (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)))
    (ZF : ZetaZeroFacts)
    (conv :
      ZeroPoleLocalUniformConvergenceAPI
        defaultZeroMultiplicityData defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (h_tsum_principalPart :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          (fun s : ℂ =>
            ∑' q : PrimePowerPair,
              q.weightC *
                (displacementCanonicalKernel (heatKernelG 1)) q.center s)
          W.s0
          (-(groupedResidueCoeff defaultZeroMultiplicityData
              (pairGroupedPoleClass defaultZeroMultiplicityData W))))
    (hpoint :
      ∀ W : ZeroWitness,
        let c : ℂ :=
          -(groupedResidueCoeff defaultZeroMultiplicityData
              (pairGroupedPoleClass defaultZeroMultiplicityData W))
        let hBreg :=
          Classical.choose
            ((designedY_BPP_pair_from_tsum defaultZeroMultiplicityData
                h_tsum_principalPart).h_Bshared_principalPart W)
        let hZreg :=
          Classical.choose
            (zside_pair_principalPart_from_convergence
              defaultZeroMultiplicityData
              (ZpoleSeries defaultZeroMultiplicityData) conv W)
        hBreg W.s0 + hZreg W.s0 =
          designedY.B.Cshared.Bshared W.s0
            + ZpoleSeries defaultZeroMultiplicityData W.s0)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC designedY.B.Cshared.Bshared z) :
    RiemannHypothesis :=
  RH_from_appendixH_interface_zeroDensity_holo
    h_real_zero_free
    hsum
    (Harch_holomorphic_from_tsumPrincipalParts_and_Bregular
      ZF
      defaultZeroMultiplicityData
      (ZpoleSeries defaultZeroMultiplicityData)
      conv
      h_tsum_principalPart
      hpoint
      hB_regular)

#check @RH_from_tsum_principalPart
#print axioms RH_from_tsum_principalPart
