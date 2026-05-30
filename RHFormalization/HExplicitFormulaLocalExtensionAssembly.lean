import RHFormalization.HExplicitFormulaWitnessCancellation

/-!
# RHFormalization.HExplicitFormulaLocalExtensionAssembly

Assemble local holomorphic extensions from two cases:

1. witness points `z = W.s0`;
2. regular points away from all witnesses.

This is not an RH endpoint.  It splits the current H/E holomorphy target into
the exact local cases that remain to be proved.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Local extensions on Ω follow from:
* local extensions at every zero witness;
* local extensions at every point that is not a zero witness.
-/
theorem Harch_local_extensions_from_witness_and_regular
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
              W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            ∃ h : ℂ → ℂ,
              HolomorphicAtC h z ∧
                LocalEqAtC h
                  (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
                  z) :
    ∀ z : ℂ,
      z ∈ Ω →
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h z ∧
            LocalEqAtC h
              (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
              z := by
  intro z hz
  by_cases hzW : ∃ W : ZeroWitness, z = W.s0
  · rcases hzW with ⟨W, rfl⟩
    exact h_witness W
  · exact h_regular z hz (by
      intro W hW
      exact hzW ⟨W, hW⟩)

/--
Global Harch holomorphy from witness and regular local extensions.
-/
theorem Harch_holomorphic_from_witness_and_regular
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
              W.s0)
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
  Harch_holomorphic_from_local_extensions
    Y
    Zpole
    (Harch_local_extensions_from_witness_and_regular
      Y Zpole h_witness h_regular)

end

end RHFormalization
