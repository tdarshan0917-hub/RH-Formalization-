import RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts
import RHFormalization.HSideResidueArithmetic
import RHFormalization.HSidePoleWitness

/-!
# RHFormalization.BsharedPrincipalPartAtWitness

D/H principal-part bridge for the shared canonical package.

The witness-cancellation and witness-branch adapters are already built.
The remaining missing input is the D/shared-side theorem:

  HasPrincipalPartAtC
    Y.B.Cshared.Bshared
    W.s0
    (-(groupedResidueCoeff M (groupedClass W))).

This file makes that obligation explicit as a narrow API and immediately wires
it into the existing witness-branch theorem.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The exact D/shared-side principal-part theorem needed at every zero witness.

This is the real upstream theorem still to be proved from the selected
construction of `Y.B.Cshared.Bshared`.
-/
structure BsharedOppositePrincipalPartData
    (Y : DDetailedConstructionWithOperatorLegality)
    (M : ZeroMultiplicityData) where
  groupedClass :
    ∀ W : ZeroWitness, GroupedPoleClass M W
  h_Bshared_principalPart :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        Y.B.Cshared.Bshared
        W.s0
        (-(groupedResidueCoeff M (groupedClass W)))

/--
Use Bshared opposite-principal-part data, together with Zpole principal parts and
point-value compatibility, to build the witness local-extension branch.
-/
theorem Harch_witness_extensions_from_BsharedPrincipalPartData
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (M : ZeroMultiplicityData)
    (BPP : BsharedOppositePrincipalPartData Y M)
    (hZ :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC
          Zpole
          W.s0
          (- (-(groupedResidueCoeff M (BPP.groupedClass W)))))
    (hpoint :
      ∀ W : ZeroWitness,
        let c : ℂ := -(groupedResidueCoeff M (BPP.groupedClass W))
        let hBreg := Classical.choose (BPP.h_Bshared_principalPart W)
        let hZreg := Classical.choose (hZ W)
        hBreg W.s0 + hZreg W.s0 =
          Y.B.Cshared.Bshared W.s0 + Zpole W.s0) :
    ∀ W : ZeroWitness,
      ∃ h : ℂ → ℂ,
        HolomorphicAtC h W.s0 ∧
          LocalEqAtC h
            (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
            W.s0 :=
  Harch_witness_extensions_from_Bshared_opposite_principalParts
    Y
    Zpole
    M
    BPP.groupedClass
    BPP.h_Bshared_principalPart
    hZ
    hpoint

end

end RHFormalization
