import RHFormalization.HExplicitFormulaLocalExtensionAssembly

/-!
# RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts

Witness-branch assembly for the H/E explicit-formula holomorphy proof.

The generic local cancellation lemma is already built. This file specializes the
witness branch to the actual principal-part data:

* `Zpole` has grouped residue coefficient;
* `Y.B.Cshared.Bshared` has the opposite coefficient.

This is not an RH endpoint.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Local extensions at every zero witness from opposite principal parts.

The remaining serious input here is the D/shared-side principal part theorem:
`Y.B.Cshared.Bshared` has coefficient `-(groupedResidueCoeff ...)`.
-/
theorem Harch_witness_extensions_from_Bshared_opposite_principalParts
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (M : ZeroMultiplicityData)
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
          Y.B.Cshared.Bshared W.s0 + Zpole W.s0) :
    ∀ W : ZeroWitness,
      ∃ h : ℂ → ℂ,
        HolomorphicAtC h W.s0 ∧
          LocalEqAtC h
            (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
            W.s0 := by
  intro W
  exact
    Harch_local_extension_at_witness_from_cancelled_principal_parts
      Y
      Zpole
      W
      (-(groupedResidueCoeff M (groupedClass W)))
      (hB W)
      (hZ W)
      (by
        simpa using hpoint W)

/--
Global Harch holomorphy from:
* witness-side opposite principal parts;
* regular-point local holomorphy away from all zero witnesses.
-/
theorem Harch_holomorphic_from_principalParts_and_regular
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (M : ZeroMultiplicityData)
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
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            ∃ h : ℂ → ℂ,
              HolomorphicAtC h z ∧
                LocalEqAtC h
                  (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
                  z) :
    HolomorphicOnC
      (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
      Ω :=
  Harch_holomorphic_from_witness_and_regular
    Y
    Zpole
    (Harch_witness_extensions_from_Bshared_opposite_principalParts
      Y Zpole M groupedClass hB hZ hpoint)
    h_regular

end

end RHFormalization
