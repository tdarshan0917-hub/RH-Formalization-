import RHFormalization.HExplicitFormulaLocalCancellation

/-!
# RHFormalization.HExplicitFormulaWitnessCancellation

Witness-level specialization of the H/E local cancellation lemma.

After `HExplicitFormulaLocalCancellation`, the generic local algebra is done.
This file specializes it to

  f := Y.B.Cshared.Bshared
  g := Zpole
  z := W.s0

using opposite principal parts.

This is not an RH endpoint.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
At a zero witness `W`, if `Y.B.Cshared.Bshared` and `Zpole` have opposite
simple principal parts, then their sum has a local holomorphic extension.

The point-value hypothesis is necessary because the project definition of
`HasPrincipalPartAtC` is punctured-neighborhood data.
-/
theorem Harch_local_extension_at_witness_from_cancelled_principal_parts
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (W : ZeroWitness)
    (c : ℂ)
    (hB :
      HasPrincipalPartAtC
        Y.B.Cshared.Bshared
        W.s0
        c)
    (hZ :
      HasPrincipalPartAtC
        Zpole
        W.s0
        (-c))
    (hpoint :
      let hBreg := Classical.choose hB
      let hZreg := Classical.choose hZ
      hBreg W.s0 + hZreg W.s0 =
        Y.B.Cshared.Bshared W.s0 + Zpole W.s0) :
    ∃ h : ℂ → ℂ,
      HolomorphicAtC h W.s0 ∧
        LocalEqAtC h
          (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
          W.s0 := by
  classical

  let hBreg : ℂ → ℂ := Classical.choose hB
  let hZreg : ℂ → ℂ := Classical.choose hZ

  have hBreg_holo :
      HolomorphicAtC hBreg W.s0 := by
    dsimp [hBreg]
    exact (Classical.choose_spec hB).1

  have hBpp :
      ∀ᶠ w in 𝓝 W.s0,
        w ≠ W.s0 →
          Y.B.Cshared.Bshared w =
            c / (w - W.s0) + hBreg w := by
    dsimp [hBreg]
    exact (Classical.choose_spec hB).2

  have hZreg_holo :
      HolomorphicAtC hZreg W.s0 := by
    dsimp [hZreg]
    exact (Classical.choose_spec hZ).1

  have hZpp :
      ∀ᶠ w in 𝓝 W.s0,
        w ≠ W.s0 →
          Zpole w =
            (-c) / (w - W.s0) + hZreg w := by
    dsimp [hZreg]
    exact (Classical.choose_spec hZ).2

  exact
    local_holomorphic_extension_add_of_cancelled_principal_parts
      Y.B.Cshared.Bshared
      Zpole
      hBreg
      hZreg
      W.s0
      c
      hBreg_holo
      hZreg_holo
      hBpp
      hZpp
      (by
        simpa [hBreg, hZreg] using hpoint)

end

end RHFormalization
