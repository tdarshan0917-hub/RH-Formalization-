import RHFormalization.ExplicitFormulaLocalReduction
import RHFormalization.ExplicitPrimePackageIdentity

/-!
# RHFormalization.ExplicitFormulaBRegular

EF6-BREG: discharge the regular-point B-side holomorphy obligation.

The designed shared B-function is definitionally the concrete prime-power tsum.
For the current displacement kernel,

  displacementCanonicalKernel G = fun a _s => G a,

so the whole prime-side `Bshared` function is constant in the complex variable
`s`. Hence it is holomorphic at every point.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
The designed Bshared function is holomorphic at every point.

Reason: after unfolding the concrete prime-power package and
`displacementCanonicalKernel`, it is a constant function of `s`.
-/
theorem designedY_Bshared_holomorphicAt
    (z : ℂ) :
    HolomorphicAtC designedY.B.Cshared.Bshared z := by
  let c : ℂ :=
    ∑' q : PrimePowerPair,
      q.weightC * heatKernelG 1 q.center
  have hc : HolomorphicAtC (fun _ : ℂ => c) z := by
    exact analyticAt_const
  refine holomorphicAtC_congr hc ?_
  filter_upwards with s
  dsimp [c]
  rw [designedY_Cshared_Bshared_eq_tsum_global s]
  simp [displacementCanonicalKernel]

/--
The regular-branch B-side hypothesis required by EF5 is automatically true.
-/
theorem designedY_Bshared_regular :
    ∀ z : ℂ,
      z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC designedY.B.Cshared.Bshared z := by
  intro z _hzΩ _hnotW
  exact designedY_Bshared_holomorphicAt z

/--
EF6-BREG: V9 local-EF theorem with the `hB_regular` hypothesis discharged.

The remaining explicit-formula local obligations are now:

1. concrete prime-power tsum opposite principal parts at witness points;
2. witness point-value compatibility.
-/
theorem RH_from_designed_D_zero_density_localEF_noBregular
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
            ZpoleSeries defaultZeroMultiplicityData W.s0) :
    RiemannHypothesis :=
  RH_from_designed_D_zero_density_localEF
    h_real_zero_free
    hsum
    h_tsum_principalPart
    hpoint
    designedY_Bshared_regular

#print axioms designedY_Bshared_holomorphicAt
#print axioms designedY_Bshared_regular
#print axioms RH_from_designed_D_zero_density_localEF_noBregular

end

end RHFormalization
