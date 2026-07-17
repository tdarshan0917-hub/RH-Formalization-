import RHFormalization.MeromorphyAssembly
import RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts

/-!
# RHFormalization.ExplicitFormulaRegularBranch

Regular-point branch for the explicit-formula holomorphy campaign.

This file does not create a new RH endpoint. It proves that away from all
zero-witness pole points, local holomorphic extensions of `Bshared + Zpole`
follow from:

* regular B-side holomorphy; and
* the already-banked analyticity of `Zpole` away from the pole set.

The only extra geometric input needed is `ZF : ZetaZeroFacts`, because
`mkZeroWitness` requires it.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
If a point of Ω is not any zero-witness pole point, then it is not in the
zero-pole set.

The proof uses the slit-plane geometry theorem
`offCritical_of_polePoint_mem_Omega`: any pole point lying in Ω comes from an
off-critical zero, hence gives a `ZeroWitness`.
-/
theorem not_zeroPoleSet_of_not_zeroWitness
    (ZF : ZetaZeroFacts)
    (z : ℂ)
    (hzΩ : z ∈ Ω)
    (hnotW : ∀ W : ZeroWitness, z ≠ W.s0) :
    z ∉ ZeroPoleSet := by
  intro hzPole
  rcases hzPole with ⟨ρ, hρ, rfl⟩
  have hoffI : IsOffCritical ρ :=
    offCritical_of_polePoint_mem_Omega ρ hρ hzΩ
  have hoff : ρ.re ≠ 1 / 2 := by
    simpa [IsOffCritical] using hoffI
  exact hnotW (mkZeroWitness ZF ρ hρ hoff) rfl

/--
Regular branch: away from witness pole points, `Bshared + Zpole` has a local
holomorphic extension, provided the B-side is holomorphic there.

The Z-side analyticity is already supplied by `zpole_analyticAt_nonpole`.
-/
theorem regular_branch_from_Bregular
    (ZF : ZetaZeroFacts)
    (Y : DDetailedConstructionWithOperatorLegality)
    (M : ZeroMultiplicityData)
    (Zpole : ℂ → ℂ)
    (conv : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC Y.B.Cshared.Bshared z) :
    ∀ z : ℂ,
      z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          ∃ h : ℂ → ℂ,
            HolomorphicAtC h z ∧
              LocalEqAtC h
                (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
                z := by
  intro z hzΩ hnotW
  have hznp : z ∉ ZeroPoleSet :=
    not_zeroPoleSet_of_not_zeroWitness ZF z hzΩ hnotW
  have hB : HolomorphicAtC Y.B.Cshared.Bshared z :=
    hB_regular z hzΩ hnotW
  have hZ : HolomorphicAtC Zpole z := by
    simpa [HolomorphicAtC] using
      (zpole_analyticAt_nonpole M Zpole conv z hzΩ hznp)
  refine ⟨fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s, ?_, ?_⟩
  · exact hB.add hZ
  · exact Filter.EventuallyEq.rfl

#print axioms not_zeroPoleSet_of_not_zeroWitness
#print axioms regular_branch_from_Bregular

end

end RHFormalization
